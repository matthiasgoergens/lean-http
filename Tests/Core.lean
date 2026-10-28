import Tests.Support.Traces
import Tests.Support.Explore

/-!
# Executable verification of the exchange core

```
core-tests traces              known defects as fixed traces
core-tests props <runs> <seed> properties at every step of random event sequences
core-tests explore <depth>     bounded breadth-first exploration over a small alphabet
```

Each prints one line per trace, run summary or search, and exits with status 1 if anything failed.
A failing random run is shrunk and printed step by step.
-/

open Std.Http LeanHttp

/-- Prints `events` on case `c`, with the actions of every step. -/
def printSteps (c : Case) (events : Array (Nat × ExchangeEvent)) : IO Unit := do
  let .ok prepared := c.prepare | IO.println "  (refused)"
  let (ex, actions) := Exchange.begin prepared 0 c.deadline
  IO.println s!"  begin at 0 -> {actions.toList.map renderAction}"
  let mut ex := ex
  for (now, event) in events do
    let (ex', actions) := ex.step now event
    IO.println s!"  at {now}: {renderEvent event} -> {actions.toList.map renderAction}"
    ex := ex'

/-- Runs the traces. -/
def runTraces : IO UInt32 := do
  let mut failing := 0
  for t in traces do
    let problems := runTrace t
    if problems.isEmpty then
      IO.println s!"PASS {t.name}"
    else
      failing := failing + 1
      IO.println s!"FAIL {t.name}"
      for p in problems do IO.println p
  IO.println s!"{traces.length} traces, {failing} failing"
  return if failing == 0 then 0 else 1

/-- A coarse name for how a run ended. -/
def endName : Option ExchangeAction → String
  | some (.finish r) => s!"finish reusable={r}"
  | some (.fail f) => s!"fail: {(f.cause.describe.splitOn ":").head!} [{f.delivery.name}]"
  | _ => "no end within the step limit"

/-- Runs `n` random sequences from `seed`. -/
def runProps (n seed : Nat) : IO UInt32 := do
  let mut rng : Rng := ⟨seed.toUInt64⟩
  let mut steps := 0
  let mut adversarial := 0
  let mut earlyHeads := 0
  let mut drains := 0
  let mut ends : Std.HashMap String Nat := {}
  let mut perScript : Std.HashMap String Nat := {}
  for i in [0:n] do
    let (c, r) := genCase.run rng
    let (res, r) := (genRun c).run r
    rng := r
    steps := steps + res.steps
    if res.adversarial then adversarial := adversarial + 1
    if res.earlyHead then earlyHeads := earlyHeads + 1
    if res.drained then drains := drains + 1
    let e := endName res.ended
    ends := ends.insert e (ends.getD e 0 + 1)
    let sn := scripts[c.script]!.name
    perScript := perScript.insert sn (perScript.getD sn 0 + 1)
    if let some (idx, v) := res.violation then
      IO.println s!"FAIL run {i} (seed {seed}), step {idx}: {v.property}: {v.detail}"
      IO.println s!"  case: {c.describe}"
      let small := shrink c res.events v.property
      let detail := match replay c small with
        | some (_, v) => s!"{v.property}: {v.detail}"
        | none => "(the shrunk sequence passes)"
      IO.println s!"  shrunk from {res.events.size} to {small.size} events, failing {detail}:"
      printSteps c small
      return 1
  IO.println s!"PASS {n} runs from seed {seed}: {steps} steps checked"
  IO.println s!"  runs with bytes sent when no response could be due: {adversarial}"
  IO.println s!"  runs with a final head before the request was written in full: {earlyHeads}"
  IO.println s!"  runs that drained an abandoned body: {drains}"
  let sorted := ends.toList.toArray.qsort (fun a b => a.2 > b.2)
  for (e, k) in sorted do
    IO.println s!"  ended {e}: {k}"
  let sortedScripts := perScript.toList.toArray.qsort (fun a b => a.1 < b.1)
  IO.println s!"  runs per script: {sortedScripts.toList.map fun (s, k) => s!"{s}={k}"}"
  return 0

/-- Runs every search to `depth`. -/
def runExplore (depth : Nat) : IO UInt32 := do
  let mut failing := 0
  let mut totalStates := 0
  let mut totalTransitions := 0
  for s in searches do
    let r := explore s depth
    totalStates := totalStates + r.states
    totalTransitions := totalTransitions + r.transitions
    match r.violation with
    | none =>
      IO.println (s!"PASS {s.name}: {r.states} states, {r.transitions} steps checked, " ++
        s!"{r.terminals} terminal ({r.reusableEnds} reusable); new states per depth {r.perDepth}")
    | some (path, v) =>
      failing := failing + 1
      IO.println s!"FAIL {s.name}: {v.property}: {v.detail}"
      printSteps s.case path
  IO.println (s!"{searches.length} searches to depth {depth}: {totalStates} states, " ++
    s!"{totalTransitions} steps checked, {failing} failing")
  return if failing == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["traces"] => runTraces
  | ["props", n, seed] => runProps n.toNat! seed.toNat!
  | ["explore", depth] => runExplore depth.toNat!
  | _ =>
    IO.eprintln "usage: core-tests traces | props <runs> <seed> | explore <depth>"
    return 2
