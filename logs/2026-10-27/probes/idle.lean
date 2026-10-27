import Std.Async
import Std.Data.HashMap
open Std Async TCP Socket Net

/-- Run an `Async` action from `IO`, catching errors. -/
def run (x : Async α) : IO (Except IO.Error α) := x.block.toBaseIO

def showOpt : Except IO.Error (Option (Option ByteArray)) → String
  | .error e => s!"error({e})"
  | .ok none => "NOT-READY(none)"
  | .ok (some none) => "READY: EOF"
  | .ok (some (some b)) => s!"READY: {b.size} bytes {String.fromUTF8! b}"

def showRecv : Except IO.Error (Option ByteArray) → String
  | .error e => s!"error({e})"
  | .ok none => "EOF"
  | .ok (some b) => s!"{b.size} bytes {String.fromUTF8! b}"

def ms (ns : Nat) : String := s!"{ns / 1000}us"

def timed (x : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let r ← x
  let t1 ← IO.monoNanosNow
  return (r, t1 - t0)

/-- `recv?` raced against a timeout; returns "TIMEOUT" if nothing within `t` ms. -/
def recvWithTimeout (s : Client) (t : Nat) : Async String := do
  let sl ← Selector.sleep ⟨t⟩
  Selectable.one #[
    .case (Client.recvSelector s 4096) fun r => pure (match r with | none => "EOF" | some b => s!"{b.size} bytes {String.fromUTF8! b}"),
    .case sl fun _ => pure "TIMEOUT"]

def main (args : List String) : IO UInt32 := do
  let port := args[0]!.toNat!
  let mode := args[1]!
  let delay := args[2]!.toNat!
  if mode == "first" then
    -- N fresh connections; one tryFn call per connection, delay after the server's action
    let n := args[3]!.toNat!
    let mut tally : Std.HashMap String Nat := {}
    let mut times : Array Nat := #[]
    for _ in [0:n] do
      let s ← Client.mk
      let addr := SocketAddress.v4 ⟨IPv4Addr.ofParts 127 0 0 1, port.toUInt16⟩
      (do s.connect addr; s.send "ping".toUTF8 : Async Unit).block
      let _ ← (s.recv? 16).block
      IO.sleep delay.toUInt32
      let (r, t) ← timed (run (Client.recvSelector s 4096).tryFn)
      let k := match r with
        | .error _ => "error" | .ok none => "NOT-READY" | .ok (some none) => "READY:EOF" | .ok (some (some _)) => "READY:data"
      tally := tally.insert k (tally.getD k 0 + 1)
      times := times.push t
    IO.println s!"first tryFn call on {n} fresh connections (delay {delay} ms after server action): {tally.toList}"
    let sorted := times.qsort (· < ·)
    IO.println s!"tryFn time: min {ms sorted[0]!}, median {ms sorted[n/2]!}, max {ms sorted[n-1]!}"
    return 0
  if mode == "latency" then
    -- N fresh connections; after the server's action, start `waitReadable` and spin on `isResolved`:
    -- how long until the loop thread has resolved it?  (capped at 50 ms; `none` scenario never resolves)
    let n := args[3]!.toNat!
    let mut times : Array Nat := #[]
    let mut capped := 0
    for _ in [0:n] do
      let s ← Client.mk
      let addr := SocketAddress.v4 ⟨IPv4Addr.ofParts 127 0 0 1, port.toUInt16⟩
      (do s.connect addr; s.send "ping".toUTF8 : Async Unit).block
      let _ ← (s.recv? 16).block
      IO.sleep delay.toUInt32
      let t0 ← IO.monoNanosNow
      let w ← s.native.waitReadable
      let mut done := false
      let mut el := 0
      while !done do
        if ← w.isResolved then done := true
        el := (← IO.monoNanosNow) - t0
        if el > 50000000 then break
      if done then times := times.push el else capped := capped + 1
      s.native.cancelRecv
    let sorted := times.qsort (· < ·)
    if sorted.size > 0 then
      IO.println s!"waitReadable resolved after (spinning on isResolved): n={sorted.size} min {ms sorted[0]!}, median {ms sorted[sorted.size/2]!}, p95 {ms sorted[sorted.size*95/100]!}, max {ms sorted[sorted.size-1]!}; not resolved within 50 ms: {capped}"
    else IO.println s!"waitReadable never resolved within 50 ms in {capped} of {n} connections"
    return 0
  let s ← Client.mk
  let addr := SocketAddress.v4 ⟨IPv4Addr.ofParts 127 0 0 1, port.toUInt16⟩
  (do s.connect addr; s.send "ping".toUTF8 : Async Unit).block
  let pong ← (s.recv? 16).block
  IO.println s!"exchange: got {showRecv (.ok pong)}"
  IO.sleep delay.toUInt32
  match mode with
  | "once" =>
    let (r, t) ← timed (run (Client.recvSelector s 4096).tryFn)
    IO.println s!"tryFn#1: {showOpt r} in {ms t}"
    -- is a read still registered?  waitReadable fails with EALREADY if so
    let w ← (s.native.waitReadable).toBaseIO
    match w with
    | .error e => IO.println s!"after tryFn: waitReadable -> error {e}  (EALREADY would mean a pending read; anything else is another cause)"
    | .ok _ => IO.println "after tryFn: waitReadable accepted (no read was registered); cancelling it"; s.native.cancelRecv
    -- is data still there?
    let (r2, t2) ← timed (run (recvWithTimeout s 1000))
    IO.println s!"then recv?-with-1s-timeout: {showRecv' r2} in {ms t2}"
  | "loop" =>
    -- repeated tight tryFn calls until something is ready
    let n := 2000
    let mut hit := false
    let t0 ← IO.monoNanosNow
    for i in [0:n] do
      if hit then break
      let r ← run (Client.recvSelector s 4096).tryFn
      match r with
      | .ok none => pure ()
      | _ => IO.println s!"tryFn call #{i+1}: {showOpt r}"; hit := true
    let t1 ← IO.monoNanosNow
    unless hit do IO.println s!"no call of {n} reported ready"
    IO.println s!"total {ms (t1 - t0)}"
  | "spaced" =>
    -- tryFn with 1 ms sleeps in between
    let n := 100
    let mut hit := false
    let t0 ← IO.monoNanosNow
    for i in [0:n] do
      if hit then break
      let r ← run (Client.recvSelector s 4096).tryFn
      match r with
      | .ok none => IO.sleep 1
      | _ => IO.println s!"tryFn call #{i+1}: {showOpt r}"; hit := true
    let t1 ← IO.monoNanosNow
    unless hit do IO.println s!"no call of {n} reported ready"
    IO.println s!"total {ms (t1 - t0)}"
  | "wait" =>
    -- the registration path: recv selector alone (via Selectable.one) with a 1 s timeout alternative
    let (r, t) ← timed (run (recvWithTimeout s 1000))
    IO.println s!"Selectable.one [recv, 1s timeout]: {showRecv' r} in {ms t}"
  | "ready" =>
    -- recv selector vs an immediately ready alternative, 200 trials
    let readyAlt : Selector Unit := { tryFn := pure (some ()), registerFn := fun _ => pure (), unregisterFn := pure () }
    let mut recvWins := 0
    let mut readyWins := 0
    let mut other := 0
    for _ in [0:200] do
      let r ← run (Selectable.one #[
        .case (Client.recvSelector s 4096) fun _ => pure "recv",
        .case readyAlt fun _ => pure "ready"])
      match r with
      | .ok "recv" => recvWins := recvWins + 1
      | .ok "ready" => readyWins := readyWins + 1
      | _ => other := other + 1
    IO.println s!"recv won {recvWins}, immediately-ready alternative won {readyWins}, other {other}"
  | _ => IO.println "bad mode"
  return 0
where showRecv' : Except IO.Error String → String
  | .error e => s!"error({e})"
  | .ok s => s
