import Tests.Support.Traces
import Tests.Support.Explore
import Tests.Support.MachineCore

/-!
# Executable verification of the exchange core

```
core-tests traces              known defects as fixed traces
core-tests props <runs> <seed> properties at every step of random event sequences
core-tests explore <depth>     bounded breadth-first exploration over a small alphabet
core-tests compare <runs> <seed> random event sequences replayed on the former core too
```

`compare` generates random runs as `props` does (without checking them), replays each run's events
on the former exchange core over the vendored machine (`Tests/Support/MachineCore.lean`), writing
the same request bytes, and compares how the two ended: the end action (with the failure's cause and delivery), the status of
the head delivered and the body delivered.  It prints the agreements and every class of
disagreement, with examples; differences are findings to explain, not failures.

`props` and `explore` take `--skip <property>` (repeatable) to leave a property unchecked, for
positive controls that show another property catching a planted bug on its own.

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
def runProps (n seed : Nat) (skip : List String) : IO UInt32 := do
  let mut rng : Rng := ⟨seed.toUInt64⟩
  let mut steps := 0
  let mut adversarial := 0
  let mut earlyHeads := 0
  let mut drains := 0
  let mut ends : Std.HashMap String Nat := {}
  let mut perScript : Std.HashMap String Nat := {}
  for i in [0:n] do
    let (c, r) := genCase.run rng
    let (res, r) := (genRun c skip).run r
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
      let small := shrink c res.events v.property skip
      let detail := match replay c small skip with
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

/-- How a run ended, comparably: the end action, the status of the head delivered and the body. -/
def outcome (actions : Array ExchangeAction) : String := Id.run do
  let mut head := "none"
  let mut body := 0
  let mut ended := "no end"
  for a in actions do
    match a with
    | .deliverHead h => head := toString h.status.toCode
    | .deliverBody b => body := body + b.size
    | .finish r => ended := s!"finish reusable={r}"
    | .fail f => ended := s!"fail {f.cause.describe} [{f.delivery.name}]"
    | _ => pure ()
  return s!"{ended}, head {head}, body {body}"

/-- The actions of the exchange core over `events` on case `c`, `begin` included. -/
def coreActions (c : Case) (events : Array (Nat × ExchangeEvent)) : Array ExchangeAction := Id.run do
  let .ok prepared := c.prepare | return #[]
  let (ex, actions) := Exchange.begin prepared 0 c.deadline
  let mut ex := ex
  let mut all := actions
  for (now, e) in events do
    let (ex', acts) := ex.step now e
    ex := ex'
    all := all ++ acts
  return all

/-- The actions of the former core over the same events. -/
def machineActions (c : Case) (events : Array (Nat × ExchangeEvent)) : Array ExchangeAction := Id.run do
  let k := c.config
  let config : MachineCore.ExchangeConfig := {
    keepAlive := k.keepAlive, maxInterim := k.maxInterim, maxBody := k.maxBody, readChunk := k.readChunk,
    readChunk_pos := k.readChunk_pos, writeChunk := k.writeChunk, gapMs := k.gapMs, gapMs_pos := k.gapMs_pos,
    drainBytes := k.drainBytes, drainMs := k.drainMs }
  let body := ByteArray.mk (Array.replicate c.bodySize 'x'.toUInt8)
  let .ok core := c.prepare | return #[]
  let .ok prepared := MachineCore.Exchange.prepare config c.head body | return #[]
  let (ex, actions) := MachineCore.Exchange.begin (prepared.writing core) 0 c.deadline
  let mut ex := ex
  let mut all := actions
  for (now, e) in events do
    let (ex', acts) := ex.step now e
    ex := ex'
    all := all ++ acts
  return all

/-- The body delivered by some actions, in bytes. -/
def bodySize (actions : Array ExchangeAction) : Nat :=
  actions.foldl (init := 0) fun n a => match a with
    | .deliverBody b => n + b.size
    | _ => n

/--
Why the two cores end a run differently, found by lifting the smallest set of these that makes them
agree:

- `body limit`: the codec refuses a chunk announced beyond it at its size line, and a body over it as
  its bytes arrive, where the former core refused either only once the caller pulled the bytes;
- `credit`: every `wantBody` made large; the core hands over everything it holds once the caller has
  credit, the former core one chunk of the machine per pull;
- `drain limit`: the drain limit lifted; the codec counts chunk data against it as the data arrives,
  the machine only once the chunk's terminator has (when the data comes in one read).

Failing that, a run that differs only in how much body was delivered, the core more, is put down to
the same timing of chunk data: the codec delivers it as it arrives.
-/
def attributeRun (c : Case) (events : Array (Nat × ExchangeEvent)) : String := Id.run do
  let agree (c : Case) (events : Array (Nat × ExchangeEvent)) :=
    outcome (coreActions c events) == outcome (machineActions c events)
  let lots := events.map fun (t, e) => match e with
    | .wantBody _ => (t, ExchangeEvent.wantBody 1000000)
    | e => (t, e)
  let variant (body credit drain : Bool) : Case × Array (Nat × ExchangeEvent) :=
    let k := c.config
    let k := if body then { k with maxBody := 2 ^ 40 } else k
    let k := if drain then { k with drainBytes := 2 ^ 40 } else k
    ({ c with config := k }, if credit then lots else events)
  let subsets : List (List String × Bool × Bool × Bool) := [
    (["body limit"], true, false, false), (["credit"], false, true, false),
    (["drain limit"], false, false, true), (["body limit", "credit"], true, true, false),
    (["body limit", "drain limit"], true, false, true), (["credit", "drain limit"], false, true, true),
    (["body limit", "credit", "drain limit"], true, true, true)]
  for (names, body, credit, drain) in subsets do
    let (c', events') := variant body credit drain
    if agree c' events' then return ", ".intercalate names
  for (_, body, credit, drain) in (([], false, false, false) :: subsets) do
    let (c', events') := variant body credit drain
    let a := coreActions c' events'
    let b := machineActions c' events'
    let ends (acts : Array ExchangeAction) := acts.filter fun
      | .finish _ | .fail _ | .deliverHead _ => true
      | _ => false
    if (ends a).toList.map renderAction == (ends b).toList.map renderAction &&
        bodySize a > bodySize b then
      return "chunk data delivered before its terminator"
  return "UNEXPLAINED"

/-- Runs `n` random sequences from `seed` on both cores and compares how they ended. -/
def runCompare (n seed : Nat) : IO UInt32 := do
  let mut rng : Rng := ⟨seed.toUInt64⟩
  let mut agree := 0
  let mut classes : Std.HashMap String (Nat × Array String) := {}
  for i in [0:n] do
    let (c, r) := genCase.run rng
    let (res, r) := (genRun c).run r
    rng := r
    let a := outcome (coreActions c res.events)
    let b := outcome (machineActions c res.events)
    if a == b then
      agree := agree + 1
    else
      let key := s!"[{attributeRun c res.events}] {scripts[c.script]!.name}: core {a} / machine {b}"
      let (k, xs) := classes.getD key (0, #[])
      let ex := s!"run {i}: {c.describe}"
      classes := classes.insert key (k + 1, if xs.size < 2 then xs.push ex else xs)
  IO.println s!"{n} runs from seed {seed}: {agree} end the same way on both cores, {n - agree} do not"
  let sorted := classes.toList.toArray.qsort (fun x y => x.1 < y.1)
  for (key, (k, xs)) in sorted do
    IO.println s!"  {k} {key}"
    for x in xs do IO.println s!"      {x}"
  return 0

/-- Prints run `k` of `compare`'s runs from `seed` step by step, on both cores. -/
def showCompare (k seed : Nat) : IO UInt32 := do
  let mut rng : Rng := ⟨seed.toUInt64⟩
  for i in [0:k + 1] do
    let (c, r) := genCase.run rng
    let (res, r) := (genRun c).run r
    rng := r
    if i == k then
      IO.println s!"run {k}: {c.describe}"
      let .ok prepared := c.prepare | return 1
      let (ex, acts) := Exchange.begin prepared 0 c.deadline
      let k' := c.config
      let config : MachineCore.ExchangeConfig := {
        keepAlive := k'.keepAlive, maxInterim := k'.maxInterim, maxBody := k'.maxBody,
        readChunk := k'.readChunk, readChunk_pos := k'.readChunk_pos, writeChunk := k'.writeChunk,
        gapMs := k'.gapMs, gapMs_pos := k'.gapMs_pos, drainBytes := k'.drainBytes, drainMs := k'.drainMs }
      let body := ByteArray.mk (Array.replicate c.bodySize 'x'.toUInt8)
      let .ok mp := MachineCore.Exchange.prepare config c.head body | return 1
      let (mx, macts) := MachineCore.Exchange.begin (mp.writing prepared) 0 c.deadline
      IO.println s!"  begin: core {acts.toList.map renderAction} / machine {macts.toList.map renderAction}"
      let mut ex := ex
      let mut mx := mx
      for (now, e) in res.events do
        let (ex', a) := ex.step now e
        let (mx', b) := mx.step now e
        ex := ex'
        mx := mx'
        let mark := if a.toList.map renderAction == b.toList.map renderAction then " " else "*"
        IO.println s!" {mark}at {now}: {renderEvent e} -> core {a.toList.map renderAction} / machine {b.toList.map renderAction}"
  return 0

/-- Runs every search to `depth`. -/
def runExplore (depth : Nat) (skip : List String) : IO UInt32 := do
  let mut failing := 0
  let mut totalStates := 0
  let mut totalTransitions := 0
  for s in searches do
    let r := explore s depth skip
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

/-- Splits `--skip <property>` options off the arguments. -/
def skipOptions : List String → List String × List String
  | "--skip" :: p :: rest => let (args, skip) := skipOptions rest; (args, p :: skip)
  | a :: rest => let (args, skip) := skipOptions rest; (a :: args, skip)
  | [] => ([], [])

def main (args : List String) : IO UInt32 := do
  let (args, skip) := skipOptions args
  unless skip.isEmpty do IO.println s!"not checking: {skip}"
  match args with
  | ["traces"] => runTraces
  | ["props", n, seed] => runProps n.toNat! seed.toNat! skip
  | ["explore", depth] => runExplore depth.toNat! skip
  | ["compare", n, seed] => runCompare n.toNat! seed.toNat!
  | ["compare-run", k, seed] => showCompare k.toNat! seed.toNat!
  | _ =>
    IO.eprintln "usage: core-tests traces | props <runs> <seed> | explore <depth> | compare <runs> <seed>"
    return 2
