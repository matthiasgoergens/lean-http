import Tests.Support.Gen

/-!
Replays one run under the checker in which an event comes earlier than a stale tick before it, to
see whether "a live exchange has a deadline ahead", which the checker states against its model's
clock (the latest time of any event), needs the shell's clock not to go backwards.

A GET whose request is written at time 0; the response head arrives at time 0, and the caller has
asked for no body, so no read is in flight and the next deadline is the exchange's own, 2000.  A tick
at 1999 is stale and changes nothing, but moves the model's clock to 1999.  Then the caller asks for
the body: at time 5, earlier than the tick, or at 1999 as a control.
-/

open Std.Http LeanHttp

def main : IO Unit := do
  for late in [5, 1999] do
    let c : Case := { script := 0, method := .get, bodySize := 0,
                      config := { keepAlive := true, gapMs := 50 }, deadline := 2000 }
    let head := "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\n".toUTF8
    let events : Array (Nat × ExchangeEvent) :=
      #[(0, .written 1000), (0, .received head), (1999, .tick), (late, .wantBody 5)]
    match replay c events with
    | none => IO.println s!"wantBody at {late}: no violation"
    | some (i, v) => IO.println s!"wantBody at {late}: step {i}: {v.property}: {v.detail}"
