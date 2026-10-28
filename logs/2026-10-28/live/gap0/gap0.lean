import Tests.Support.Gen

/-!
Replays one run under the checker with `gapMs := 0` (allowed by `Config.readGapMs`), to see whether
the checker's "a live exchange has a deadline ahead" holds when a write or read gets the deadline
`now + 0`.
-/

open Std.Http LeanHttp

def main : IO Unit := do
  for gap in [0, 1] do
    -- script 0, a POST of 100 bytes in slices of 16, the first slice completing at time 0
    let c : Case := { script := 0, method := .post, bodySize := 100,
                      config := { keepAlive := true, writeChunk := 16, gapMs := gap }, deadline := 2000 }
    let events : Array (Nat × ExchangeEvent) := #[(0, .written 16), (0, .written 16)]
    match replay c events with
    | none => IO.println s!"gapMs={gap}: no violation"
    | some (i, v) => IO.println s!"gapMs={gap}: step {i}: {v.property}: {v.detail}"
