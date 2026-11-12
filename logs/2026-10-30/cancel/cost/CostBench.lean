import LeanHttp

/-!
# A driver for interleaved timing (`costbench.py`)

`cost-bench <URL> [token]` makes one warm-up GET to URL through one client, then waits on standard
input: for each line holding a number N it makes N more GETs through the same client, one after
another, and prints one line, the number that succeeded and each call's time in nanoseconds.  With
`token`, every call is given the same cancellation token, never cancelled (only on trees whose
client takes one: `build.sh` replaces the marked line).  The configuration is net-client's with
`trace=0`: the defaults and an `observe` hook that does nothing.  The end of input ends it.

Copied into each tree by `build.sh` and built there as the executable `cost-bench`; not part of
lean-http.
-/

open Std.Http Std.Async LeanHttp

def main (args : List String) : IO UInt32 := do
  let some url := args.head? | do IO.eprintln "usage: cost-bench <URL> [token]"; return 2
  let some uri := URI.parse? url | do IO.eprintln s!"cannot parse {url}"; return 2
  let withToken := args.contains "token"
  let req : Request ByteArray :=
    { line := { method := .get, version := .v11, uri := .absoluteForm uri, headers := .empty },
      body := .empty }
  let client ← Client.new { observe := some fun _ _ => pure () }
  let token ← Std.CancellationToken.new
  let call : IO (Except Error (Response ByteArray)) :=
    (client.request req).block -- CALL
  let _ := withToken; let _ := token
  discard call
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let n := (String.ofList (line.toList.filter Char.isDigit)).toNat!
    let mut times : Array Nat := #[]
    let mut oks := 0
    for _ in [0:n] do
      let t0 ← IO.monoNanosNow
      let r ← call
      let t1 ← IO.monoNanosNow
      times := times.push (t1 - t0)
      if r matches .ok _ then oks := oks + 1
    stdout.putStrLn s!"{oks} {" ".intercalate (times.toList.map toString)}"
    stdout.flush
  return 0
