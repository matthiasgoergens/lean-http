import LeanHttp.Codec
import LeanHttp.Exchange
import Tests.Support.Drive
import Tests.Support.MachineCore

/-!
# Parsing large bodies: the exchange core, the codec alone, and the former core

Times how long each takes to parse a response with a 60 MB body, fed in 64 KiB pieces as the shell
reads them: one with a `Content-Length`, and two chunked, with 16 KiB and with 1 KiB chunks.  Three
parsers: the exchange core as the client uses it (`core`, through `Exchange.step` with `received`
events, with the credit `Client.request` gives), the codec alone (`codec`, `Parser.feed` per piece),
and the former exchange core over the vendored machine (`machine`, `Tests/Support/MachineCore.lean`,
the core the client used before it ran the codec), driven the same way.  Each only counts the body
bytes delivered, which must come to the whole body.

The cells run in randomised blocks: each block runs every cell once, in an order drawn afresh, so
that drift in the machine's load falls on all cells alike.

Usage: `codec-bench [blocks] [seed]`; prints one line per observation (`obs CELL BLOCK NS`) and a
median per cell.
-/

open Std.Http LeanHttp

/-- The size of the body, in bytes. -/
def bodySize : Nat := 60 * 1000 * 1000

/-- The size of a read. -/
def pieceSize : Nat := 64 * 1024

/-- A body of `n` bytes, not all alike. -/
def mkBody (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  for i in [0:n] do b := b.push (97 + (i % 26)).toUInt8
  return b

/-- A response with a `Content-Length` body. -/
def lengthResponse (body : ByteArray) : ByteArray :=
  s!"HTTP/1.1 200 OK\r\nContent-Type: application/octet-stream\r\nContent-Length: {body.size}\r\n\r\n".toUTF8 ++ body

/-- A chunked response carrying `body` in chunks of `chunk` bytes. -/
def chunkedResponse (body : ByteArray) (chunk : Nat) : ByteArray := Id.run do
  let mut out := "HTTP/1.1 200 OK\r\nContent-Type: application/octet-stream\r\nTransfer-Encoding: chunked\r\n\r\n".toUTF8
  let mut i := 0
  while i < body.size do
    let n := min chunk (body.size - i)
    out := out ++ s!"{String.ofList (Nat.toDigits 16 n)}\r\n".toUTF8 ++ body.extract i (i + n) ++ "\r\n".toUTF8
    i := i + n
  return out ++ "0\r\n\r\n".toUTF8

/-- `bytes` cut into reads. -/
def pieces (bytes : ByteArray) : Array ByteArray := Id.run do
  let mut out := #[]
  let mut i := 0
  while i < bytes.size do
    out := out.push (bytes.extract i (min bytes.size (i + pieceSize)))
    i := i + pieceSize
  return out

/-- The request every response answers. -/
def requestHead (method : Method) : Request.Head :=
  { method, version := .v11, uri := .originForm { segments := #[], absolute := true } none,
    headers := Headers.empty.insert Header.Name.host (.mk "example.test") }

/-- Parses with the codec; returns the body bytes delivered and whether the response ended. -/
def runCodec (input : Array ByteArray) : Nat × Bool := Id.run do
  let mut p := Codec.Parser.start {} .get
  let mut total := 0
  let mut done := false
  for piece in input do
    let (p', events) := p.feed piece
    p := p'
    for e in events do
      match e with
      | .body b => total := total + b.size
      | .done => done := true
      | _ => pure ()
  return (total, done)

/-- Parses with the former exchange core; returns the body bytes delivered and whether it finished. -/
def runMachine (input : Array ByteArray) : Nat × Bool := Id.run do
  let prepared := MachineCore.prepare! {} (requestHead .get) .empty
  let (ex, _) := MachineCore.Exchange.begin prepared 0 1000000000
  let (ex, _) := ex.step 0 (.written prepared.bytes.size)
  let (ex, _) := ex.step 0 (.wantBody (prepared.config.maxBody + 1))
  let mut ex := ex
  let mut total := 0
  let mut done := false
  for piece in input do
    let (ex', actions) := ex.step ex.now (.received piece)
    ex := ex'
    for a in actions do
      match a with
      | .deliverBody b => total := total + b.size
      | .finish _ => done := true
      | _ => pure ()
  return (total, done)

/-- Parses with the exchange core; returns the body bytes delivered and whether it finished. -/
def runCore (input : Array ByteArray) : Nat × Bool := Id.run do
  let prepared := prepare! {} (requestHead .get) .empty
  let (ex, _) := Exchange.begin prepared 0 1000000000
  let (ex, _) := ex.step 0 (.written prepared.bytes.size)
  let (ex, _) := ex.step 0 (.wantBody (prepared.config.maxBody + 1))
  let mut ex := ex
  let mut total := 0
  let mut done := false
  for piece in input do
    let (ex', actions) := ex.step ex.now (.received piece)
    ex := ex'
    for a in actions do
      match a with
      | .deliverBody b => total := total + b.size
      | .finish _ => done := true
      | _ => pure ()
  return (total, done)

/-- One cell: a name, a parser, and its input. -/
structure Cell where
  /-- The name. -/
  name : String
  /-- The parser. -/
  run : Array ByteArray → Nat × Bool
  /-- The input. -/
  input : Array ByteArray

instance : Inhabited Cell := ⟨{ name := "", run := fun _ => (0, false), input := #[] }⟩

/-- A permutation of `0 .. n - 1`, from a seed. -/
def shuffle (n : Nat) (seed : UInt64) : List Nat × UInt64 := Id.run do
  let mut xs := (List.range n).toArray
  let mut s := seed
  for i in [0:n] do
    s := s * 6364136223846793005 + 1442695040888963407
    let j := i + ((s >>> 33).toNat % (n - i))
    xs := xs.swapIfInBounds i j
  return (xs.toList, s)

def main (args : List String) : IO UInt32 := do
  let blocks := (args[0]?.bind String.toNat?).getD 10
  let seed := (args[1]?.bind String.toNat?).getD 1
  let body := mkBody bodySize
  let cl := pieces (lengthResponse body)
  let ch16 := pieces (chunkedResponse body (16 * 1024))
  let ch1 := pieces (chunkedResponse body 1024)
  -- In threes per workload: core, machine, codec.
  let cells : Array Cell := #[
    { name := "core-length", run := runCore, input := cl },
    { name := "machine-length", run := runMachine, input := cl },
    { name := "codec-length", run := runCodec, input := cl },
    { name := "core-chunked16k", run := runCore, input := ch16 },
    { name := "machine-chunked16k", run := runMachine, input := ch16 },
    { name := "codec-chunked16k", run := runCodec, input := ch16 },
    { name := "core-chunked1k", run := runCore, input := ch1 },
    { name := "machine-chunked1k", run := runMachine, input := ch1 },
    { name := "codec-chunked1k", run := runCodec, input := ch1 }]
  IO.println s!"body={bodySize} piece={pieceSize} blocks={blocks} seed={seed}"
  let mut times : Array (Array Nat) := cells.map fun _ => #[]
  let mut s := seed.toUInt64
  let mut failed := false
  for block in [0:blocks] do
    let (order, s') := shuffle cells.size s
    s := s'
    for k in order do
      let cell := cells[k]!
      let t0 ← IO.monoNanosNow
      let (total, done) := cell.run cell.input
      let t1 ← IO.monoNanosNow
      if total != bodySize || !done then
        IO.println s!"WRONG {cell.name}: delivered {total}, done {done}"
        failed := true
      IO.println s!"obs {cell.name} {block} {t1 - t0}"
      times := times.modify k (·.push (t1 - t0))
  for k in [0:cells.size] do
    let ts := (times[k]!.toList.mergeSort (· ≤ ·)).toArray
    let median := ts[ts.size / 2]!
    IO.println s!"median {cells[k]!.name} {median / 1000000} ms (min {ts[0]! / 1000000}, max {ts[ts.size - 1]! / 1000000})"
  -- Paired within blocks, per workload: the core over the former core, and the core over the codec.
  let ratio (a b : Nat) : IO Unit := do
    let num := times[a]!
    let den := times[b]!
    let ratios := (List.range num.size).map fun k => (num[k]!.toFloat / den[k]!.toFloat)
    let rs := (ratios.mergeSort (· ≤ ·)).toArray
    let q (f : Float) := rs[(f * (rs.size - 1).toFloat).toUInt64.toNat]!
    let faster := ratios.filter (· < 1) |>.length
    IO.println s!"ratio {cells[a]!.name}/{cells[b]!.name}: median {q 0.5}, quartiles {q 0.25} {q 0.75}, range {q 0} {q 1}; {cells[a]!.name} faster in {faster} of {rs.size} blocks"
  for w in [0:cells.size / 3] do
    ratio (3 * w) (3 * w + 1)
    ratio (3 * w) (3 * w + 2)
  return if failed then 1 else 0
