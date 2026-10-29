import LeanHttp.Pool
import Tests.Support.Gen

/-!
# Executable verification of the pool core

```
pool-tests traces                       fixed scenarios with their expected results
pool-tests props <runs> <seed> [plant]  properties after every operation of random sequences
pool-tests explore <depth> [plant]      bounded breadth-first exploration over a small alphabet
pool-tests control <runs> <seed> <depth> every planted bug, each of which must be caught
```

Every operation is checked against a model written separately from the pool (`Model`): a table from
connection to state (idle with origin and time, checked out with origin, gone) and the order in
which connections went idle.  After each operation the checker compares the pool's result and
contents with the model's and checks the properties `LeanHttp.Pool.Proofs` proves, each by name, so
that a failure says which property broke:

- `invariant`: no connection both idle and checked out or twice in either, every one allocated, the
  idle and active caps, nothing idle once closed;
- `reused other than a live idle connection`: `take` reused only an idle connection of the origin,
  not expired at `now`;
- `given back while not checked out`: `giveBack` and `drop` take back only a checked-out connection,
  and leave the pool as `sweep` would otherwise;
- `gone came back`: a gone connection is never idle or checked out again, and a new connection's id
  was never allocated before;
- `agrees with the model`: results, idle and checked-out connections, next id and closed flag.

`plant` runs the checks over a copy of the pool with a bug planted (`Plant`), as a positive control:
`control` runs every plant through random runs and exploration, with every check and with the
properties alone (no comparison with the model), and fails unless each catches it.
A failing random run is shrunk by deleting operations while the same property fails.
-/

open LeanHttp

namespace PoolTests

/-- Origins are strings, as in the shell. -/
abbrev P := Pool String

/-! ## The model -/

/-- A connection's state in the model. -/
inductive MState where
  | idle (origin : String) (since : Nat)
  | out (origin : String)
  | gone
deriving Repr, BEq, Inhabited

/-- The model: every allocated connection's state, the order of the idle ones, the next id. -/
structure Model where
  config : PoolConfig
  states : Array MState := #[]
  /-- Idle connections, most recently given back first. -/
  order : List Nat := []
  closed : Bool := false
deriving Inhabited

namespace Model

def get (m : Model) (id : Nat) : Option MState := m.states[id]?

def set (m : Model) (id : Nat) (s : MState) : Model :=
  let order := m.order.filter (· != id)
  let order := match s with
    | .idle .. => id :: order
    | _ => order
  { m with states := m.states.set! id s, order }

def isOut (m : Model) (id : Nat) : Bool :=
  match m.get id with
  | some (.out _) => true
  | _ => false

def countIdle (m : Model) (origin : String) : Nat :=
  m.order.filter (fun id => match m.get id with | some (.idle o _) => o == origin | _ => false) |>.length

def countOut (m : Model) (origin : String) : Nat :=
  m.states.toList.filter (fun s => match s with | .out o => o == origin | _ => false) |>.length

/-- Expires the idle connections at `now`; returns them. -/
def expire (m : Model) (now : Nat) : Model × List Nat := Id.run do
  let mut m := m
  let mut gone := []
  for id in m.order do
    if let some (.idle _ since) := m.get id then
      if since + m.config.idleTimeoutMs ≤ now then
        m := m.set id .gone
        gone := id :: gone
  return (m, gone)

def take (m : Model) (origin : String) (now : Nat) (reuse : Bool) : Model × Taken × List Nat :=
  let (m, gone) := m.expire now
  if m.closed then (m, .closed, gone)
  else if m.config.maxActive.any (· ≤ m.countOut origin) then (m, .atCap, gone)
  else
    let candidate := if reuse then
        m.order.find? (fun id => match m.get id with | some (.idle o _) => o == origin | _ => false)
      else none
    match candidate with
    | some id => (m.set id (.out origin), .reuse id, gone)
    | none =>
      let id := m.states.size
      ({ m with states := m.states.push (.out origin) }, .fresh id, gone)

def giveBack (m : Model) (id : Nat) (reusable : Bool) (now : Nat) : Model × Returned × List Nat :=
  let (m, gone) := m.expire now
  match m.get id with
  | some (.out origin) =>
    if reusable && !m.closed && m.countIdle origin < m.config.maxIdle then
      (m.set id (.idle origin now), .idle, gone)
    else (m.set id .gone, .dropped, gone)
  | _ => (m, .notOut, gone)

def drop (m : Model) (id : Nat) : Model × Bool :=
  if m.isOut id then (m.set id .gone, true) else (m, false)

def closeAll (m : Model) : Model × List Nat :=
  let ids := m.order
  ({ (ids.foldl (fun m id => m.set id .gone) m) with closed := true }, ids)

end Model

/-! ## Planted bugs -/

/-- A bug planted in a copy of the pool, for positive controls. -/
inductive Plant where
  /-- `take` ignores the clock, so expired connections are reused. -/
  | ignoreClock
  /-- `giveBack` of a connection that is not checked out makes it idle anyway. -/
  | acceptAny
  /-- `giveBack` keeps one idle connection more than the cap. -/
  | capOffByOne
  /-- `giveBack` ignores the reuse verdict. -/
  | ignoreVerdict
  /-- `drop` leaves the connection checked out. -/
  | dropKeeps
deriving Repr, BEq, Inhabited

def Plant.all : List Plant := [.ignoreClock, .acceptAny, .capOffByOne, .ignoreVerdict, .dropKeeps]

def Plant.name : Plant → String
  | .ignoreClock => "ignore-clock"
  | .acceptAny => "accept-any"
  | .capOffByOne => "cap-off-by-one"
  | .ignoreVerdict => "ignore-verdict"
  | .dropKeeps => "drop-keeps"

def Plant.parse? (s : String) : Option Plant := Plant.all.find? (·.name == s)

/-- The pool's operations, or a copy with a planted bug. -/
structure Impl where
  take : P → String → Nat → Bool → P × Taken × List ConnId := fun p o n r => p.take o n r
  giveBack : P → ConnId → Bool → Nat → P × Returned × List ConnId :=
    fun p i r n => p.giveBack i r n
  drop : P → ConnId → P × Bool := fun p i => p.drop i
  sweep : P → Nat → P × List ConnId := fun p n => p.sweep n
  closeAll : P → P × List ConnId := fun p => p.closeAll

def Impl.ofPlant : Option Plant → Impl
  | none => {}
  | some .ignoreClock => { take := fun p o _ r => p.take o 0 r }
  | some .acceptAny => {
      giveBack := fun p i r n =>
        match p.giveBack i r n with
        | (q, .notOut, c) =>
          if i ∈ q.idleIds then (q, .notOut, c)
          else ({ q with idle := { id := i, origin := "a", since := n } :: q.idle }, .idle, c)
        | res => res }
  | some .capOffByOne => {
      giveBack := fun p i r n =>
        let (q, res, c) :=
          Pool.giveBack { p with config := { p.config with maxIdle := p.config.maxIdle + 1 } } i r n
        ({ q with config := p.config }, res, c) }
  | some .ignoreVerdict => { giveBack := fun p i _ n => p.giveBack i true n }
  | some .dropKeeps => { drop := fun p i => (p, i ∈ p.outIds) }

/-! ## Operations and checks -/

/-- An operation with its arguments (`PoolOp` over string origins). -/
abbrev Op := PoolOp String

def renderOp : Op → String
  | .take o n r => s!"take {o} at {n}{if r then "" else " (fresh)"}"
  | .giveBack i r n => s!"giveBack {i} reusable={r} at {n}"
  | .drop i => s!"drop {i}"
  | .sweep n => s!"sweep at {n}"
  | .closeAll => "closeAll"

/-- A failed check. -/
structure Violation where
  property : String
  detail : String

/-- Fails a check. -/
def violation {α : Type} (property detail : String) : Except Violation α :=
  throw { property, detail }

/-- The pool's invariant, executably. -/
def checkInvariant (p : P) : Option String := Id.run do
  let ids := p.idleIds ++ p.outIds
  if ids.eraseDups.length != ids.length then return some s!"an id twice: idle {p.idleIds}, out {p.outIds}"
  if let some id := ids.find? (· ≥ p.next) then return some s!"id {id} not below next {p.next}"
  for o in ["a", "b", "c"] do
    if p.idleCount o > p.config.maxIdle then return some s!"{p.idleCount o} idle for {o}"
    if let some m := p.config.maxActive then
      if p.activeCount o > m then return some s!"{p.activeCount o} checked out for {o}"
  if p.closed && !p.idle.isEmpty then return some "idle connections in a closed pool"
  return none

/-- Sorted, for comparing lists of ids as sets. -/
def sorted (xs : List Nat) : List Nat := xs.toArray.qsort (· < ·) |>.toList

/-- The pool's contents in the model's terms: the idle connections in order, then the checked-out ones
by id. -/
def contents (p : P) : List (Nat × MState) :=
  (p.idle.map fun c => (c.id, MState.idle c.origin c.since)) ++
    ((p.out.toArray.qsort (·.1 < ·.1)).toList.map fun (i, o) => (i, .out o))

def modelContents (m : Model) : List (Nat × MState) := Id.run do
  let mut xs := m.order.filterMap fun id => (m.get id).map (id, ·)
  for h : i in [0:m.states.size] do
    if let .out o := m.states[i] then xs := xs ++ [(i, .out o)]
  return xs

/--
Runs `op` on the pool through `impl` and on the model, and checks everything (without comparing the
pool with the model unless `modelCheck`).  Returns the new pool and model, or the first violation.
-/
def checkOp (impl : Impl) (p : P) (m : Model) (op : Op) (modelCheck : Bool := true) :
    Except Violation (P × Model) := do
  let (p', m', implRes, modelRes, implClose, modelClose) : P × Model × String × String × List Nat × List Nat :=
    match op with
    | .take o n r =>
      let (p', t, c) := impl.take p o n r
      let (m', t', c') := m.take o n r
      (p', m', reprStr t, reprStr t', c, c')
    | .giveBack i r n =>
      let (p', res, c) := impl.giveBack p i r n
      let (m', res', c') := m.giveBack i r n
      (p', m', reprStr res, reprStr res', c, c')
    | .drop i =>
      let (p', b) := impl.drop p i
      let (m', b') := m.drop i
      (p', m', toString b, toString b', [], [])
    | .sweep n =>
      let (p', c) := impl.sweep p n
      let (m', c') := m.expire n
      (p', m', "", "", c, c')
    | .closeAll =>
      let (p', c) := impl.closeAll p
      let (m', c') := m.closeAll
      (p', m', "", "", c, c')
  if let some d := checkInvariant p' then violation "invariant" d
  -- Properties, before the full comparison so that a failure names the property.
  match op with
  | .take o n r =>
    match (impl.take p o n r).2.1 with
    | .reuse i =>
      match m.get i with
      | some (.idle o' since) =>
        if o' != o then violation "reused other than a live idle connection" s!"reused {i} of origin {o'} for {o}"
        if since + p.config.idleTimeoutMs ≤ n then
          violation "reused other than a live idle connection" s!"reused {i}, idle since {since}, at {n}"
      | s => violation "reused other than a live idle connection" s!"reused {i}, which was {reprStr s}, not idle"
    | .fresh i =>
      if i < m.states.size then violation "gone came back" s!"new connection {i} was allocated before"
    | _ => pure ()
  | .giveBack i r n =>
    let (_, res, _) := impl.giveBack p i r n
    if res != .notOut && !m.isOut i then
      violation "given back while not checked out" s!"{i} taken back as {reprStr res}"
    if res == .notOut && reprStr (contents p') != reprStr (contents (p.sweep n).1) then
      violation "given back while not checked out" s!"{i} not checked out, but the pool changed"
  | .drop i =>
    let (_, b) := impl.drop p i
    if b && !m.isOut i then violation "given back while not checked out" s!"dropped {i}"
    if !b && reprStr (contents p') != reprStr (contents p) then
      violation "given back while not checked out" s!"{i} not dropped, but the pool changed"
  | _ => pure ()
  for h : i in [0:m.states.size] do
    if m.states[i] == .gone && (i ∈ p'.idleIds || i ∈ p'.outIds) then
      violation "gone came back" s!"{i} was gone and is in the pool again"
  unless modelCheck do return (p', m')
  if implRes != modelRes then violation "agrees with the model" s!"result {implRes}, model {modelRes}"
  if sorted implClose != sorted modelClose then
    violation "agrees with the model" s!"closed {implClose}, model {modelClose}"
  if reprStr (contents p') != reprStr (modelContents m') then
    violation "agrees with the model" s!"pool {reprStr (contents p')}, model {reprStr (modelContents m')}"
  if p'.next != m'.states.size || p'.closed != m'.closed then
    violation "agrees with the model" s!"next {p'.next}/{m'.states.size}, closed {p'.closed}/{m'.closed}"
  return (p', m')

/-- Replays `ops` from an empty pool; returns the index and violation of the first failure. -/
def replay (impl : Impl) (config : PoolConfig) (ops : Array Op) (modelCheck : Bool := true) :
    Option (Nat × Violation) := Id.run do
  let mut p : P := Pool.empty config
  let mut m : Model := { config }
  for h : i in [0:ops.size] do
    match checkOp impl p m ops[i] modelCheck with
    | .ok (p', m') => p := p'; m := m'
    | .error v => return some (i, v)
  return none

/-! ## Traces -/

/-- A scenario: operations, and the result each must give (`""` for no expectation). -/
structure Trace where
  name : String
  config : PoolConfig := {}
  steps : List (Op × String)

/-- The result of an operation as the traces write it. -/
def resultOf (impl : Impl) (p : P) : Op → P × String
  | .take o n r =>
    let (p', t, c) := impl.take p o n r
    (p', s!"{reprStr t}{if c.isEmpty then "" else s!" closing {c}"}")
  | .giveBack i r n =>
    let (p', res, c) := impl.giveBack p i r n
    (p', s!"{reprStr res}{if c.isEmpty then "" else s!" closing {c}"}")
  | .drop i => let (p', b) := impl.drop p i; (p', toString b)
  | .sweep n => let (p', c) := impl.sweep p n; (p', s!"closing {c}")
  | .closeAll => let (p', c) := impl.closeAll p; (p', s!"closing {c}")

def traces : List Trace := [
  { name := "a connection given back reusable is reused"
    steps := [(.take "a" 0 true, "LeanHttp.Taken.fresh 0"), (.giveBack 0 true 10, "LeanHttp.Returned.idle"),
      (.take "a" 20 true, "LeanHttp.Taken.reuse 0")] },
  { name := "a connection given back not reusable is not reused"
    steps := [(.take "a" 0 true, "LeanHttp.Taken.fresh 0"),
      (.giveBack 0 false 10, "LeanHttp.Returned.dropped"), (.take "a" 20 true, "LeanHttp.Taken.fresh 1")] },
  { name := "the idle cap: the fifth reusable connection given back is closed"
    steps := (List.range 5).map (fun i => (.take "a" 0 true, s!"LeanHttp.Taken.fresh {i}")) ++
      (List.range 4).map (fun i => (.giveBack i true 1, "LeanHttp.Returned.idle")) ++
      [(.giveBack 4 true 1, "LeanHttp.Returned.dropped")] },
  { name := "the idle timeout: reused just before it, closed at it"
    steps := [(.take "a" 0 true, "LeanHttp.Taken.fresh 0"), (.giveBack 0 true 0, "LeanHttp.Returned.idle"),
      (.take "a" 3999 true, "LeanHttp.Taken.reuse 0"), (.giveBack 0 true 4000, "LeanHttp.Returned.idle"),
      (.take "a" 8000 true, "LeanHttp.Taken.fresh 1 closing [0]")] },
  { name := "a sweep closes the expired idle connections of every origin"
    steps := [(.take "a" 0 true, ""), (.take "b" 0 true, ""), (.take "b" 0 true, ""),
      (.giveBack 0 true 0, ""), (.giveBack 1 true 0, ""), (.giveBack 2 true 3000, ""),
      (.sweep 4000, "closing [1, 0]"), (.sweep 7000, "closing [2]")] },
  { name := "a second give-back or a drop after a give-back is refused"
    steps := [(.take "a" 0 true, ""), (.giveBack 0 true 1, "LeanHttp.Returned.idle"),
      (.giveBack 0 true 2, "LeanHttp.Returned.notOut"), (.drop 0, "false"),
      (.giveBack 7 true 3, "LeanHttp.Returned.notOut"), (.drop 7, "false")] },
  { name := "a dropped connection is not reused and cannot be given back"
    steps := [(.take "a" 0 true, ""), (.drop 0, "true"), (.giveBack 0 true 1, "LeanHttp.Returned.notOut"),
      (.take "a" 2 true, "LeanHttp.Taken.fresh 1")] },
  { name := "the active cap: a take waits until a connection comes back"
    config := { maxActive := some 1 }
    steps := [(.take "a" 0 true, "LeanHttp.Taken.fresh 0"), (.take "a" 0 true, "LeanHttp.Taken.atCap"),
      (.take "b" 0 true, "LeanHttp.Taken.fresh 1"), (.giveBack 0 true 1, "LeanHttp.Returned.idle"),
      (.take "a" 2 true, "LeanHttp.Taken.reuse 0")] },
  { name := "closing: idle connections closed, later give-backs dropped, takes refused"
    steps := [(.take "a" 0 true, ""), (.take "a" 0 true, ""), (.giveBack 0 true 1, "LeanHttp.Returned.idle"),
      (.closeAll, "closing [0]"), (.giveBack 1 true 2, "LeanHttp.Returned.dropped"),
      (.take "a" 3 true, "LeanHttp.Taken.closed")] },
  { name := "the most recently given back idle connection is reused first"
    steps := [(.take "a" 0 true, ""), (.take "a" 0 true, ""), (.giveBack 1 true 1, ""),
      (.giveBack 0 true 2, ""), (.take "a" 3 true, "LeanHttp.Taken.reuse 0"),
      (.take "a" 3 true, "LeanHttp.Taken.reuse 1")] },
  { name := "origins do not share connections"
    steps := [(.take "a" 0 true, ""), (.giveBack 0 true 1, ""), (.take "b" 2 true, "LeanHttp.Taken.fresh 1"),
      (.take "a" 2 true, "LeanHttp.Taken.reuse 0")] },
  { name := "a take without reuse opens a new connection even with one idle"
    steps := [(.take "a" 0 true, ""), (.giveBack 0 true 1, ""), (.take "a" 2 false, "LeanHttp.Taken.fresh 1"),
      (.take "a" 2 true, "LeanHttp.Taken.reuse 0")] }
]

/-- Runs one trace; returns its problems. -/
def runTrace (impl : Impl) (t : Trace) : List String := Id.run do
  let mut p : P := Pool.empty t.config
  let mut m : Model := { config := t.config }
  let mut problems := []
  for (op, want) in t.steps do
    let (_, got) := resultOf impl p op
    if want != "" && got != want then
      problems := problems ++ [s!"  {renderOp op}: expected {want}, got {got}"]
    match checkOp impl p m op with
    | .ok (p', m') => p := p'; m := m'
    | .error v =>
      problems := problems ++ [s!"  {renderOp op}: {v.property}: {v.detail}"]
      return problems
  return problems

def runTraces : IO UInt32 := do
  let mut failing := 0
  for t in traces do
    let problems := runTrace {} t
    if problems.isEmpty then
      IO.println s!"PASS {t.name}"
    else
      failing := failing + 1
      IO.println s!"FAIL {t.name}"
      for p in problems do IO.println p
  IO.println s!"{traces.length} traces, {failing} failing"
  return if failing == 0 then 0 else 1

/-! ## Random runs -/

/-- A random configuration: small caps and timeout, so that they are reached often. -/
def genConfig : Gen PoolConfig := do
  let maxIdle ← below 4
  let idleTimeoutMs ← pick [0, 1, 10, 100, 1000]
  let maxActive ← pick [none, none, some 1, some 3]
  return { maxIdle, idleTimeoutMs, maxActive }

/-- A random operation in the state `(p, now)`: mostly sensible, sometimes a misuse. -/
def genOp (p : P) (now : Nat) : Gen (Op × Nat) := do
  let now := now + (← pickWeighted [(6, 0), (3, 1), (2, 5), (1, 60)])
  let anyId : Gen Nat := do
    let out := if p.outIds.isEmpty then [p.next] else p.outIds
    pickWeighted [(12, (← pick out)), (1, (← pick (p.idleIds ++ [p.next]))), (1, ← below (p.next + 2))]
  let op ← pickWeighted [
    (5, PoolOp.take (← pick ["a", "a", "b", "c"]) now ((← below 5) != 0)),
    (5, .giveBack (← anyId) ((← below 3) != 0) now),
    (2, .drop (← anyId)),
    (1, .sweep now),
    (if (← below 20) == 0 then 1 else 0, .closeAll)]
  return (op, now)

/-- One random run of up to `steps` operations; returns the operations and the first violation. -/
def genRun (impl : Impl) (config : PoolConfig) (steps : Nat) (modelCheck : Bool) :
    Gen (Array Op × Option (Nat × Violation)) := do
  let mut p : P := Pool.empty config
  let mut m : Model := { config }
  let mut now := 0
  let mut ops := #[]
  for i in [0:steps] do
    let (op, n) ← genOp p now
    now := n
    ops := ops.push op
    match checkOp impl p m op modelCheck with
    | .ok (p', m') => p := p'; m := m'
    | .error v => return (ops, some (i, v))
  return (ops, none)

def shrink (impl : Impl) (config : PoolConfig) (ops : Array Op) (property : String) (modelCheck : Bool) :
    Array Op := Id.run do
  let mut current := ops
  let mut changed := true
  while changed do
    changed := false
    let mut i := 0
    while i < current.size do
      let candidate := current.eraseIdx! i
      match replay impl config candidate modelCheck with
      | some (_, v) =>
        if v.property == property then
          current := candidate
          changed := true
        else i := i + 1
      | none => i := i + 1
  return current

/-- Runs `n` random runs from `seed`; returns the violated property, if any. -/
def runProps (impl : Impl) (n seed : Nat) (quiet : Bool := false) (modelCheck : Bool := true) :
    IO (Option String) := do
  let mut rng : Rng := ⟨seed.toUInt64⟩
  let mut ops := 0
  let mut stats : Std.HashMap String Nat := {}
  for i in [0:n] do
    let ((config, run), r) := (do
      let config ← genConfig
      return (config, ← genRun impl config 40 modelCheck) : Gen _).run rng
    rng := r
    let (seq, violation) := run
    ops := ops + seq.size
    -- What the operations did, on the pool itself, to show what the runs reach.
    let mut p : P := Pool.empty config
    for op in seq do
      let (p', k, closed) := match op with
        | .take o n r =>
          let (p', t, c) := p.take o n r
          let k := match t with
            | .reuse _ => "take: reuse" | .fresh _ => "take: fresh" | .atCap => "take: at cap"
            | .closed => "take: closed"
          (p', k, c.length)
        | .giveBack i r n =>
          let (p', res, c) := p.giveBack i r n
          let k := match res with
            | .idle => "giveBack: idle" | .dropped => if r then "giveBack: dropped (cap or closed)"
                else "giveBack: dropped (not reusable)"
            | .notOut => "giveBack: not checked out"
          (p', k, c.length)
        | .drop i =>
          let (p', b) := p.drop i
          (p', if b then "drop: dropped" else "drop: not checked out", 0)
        | .sweep n => let (p', c) := p.sweep n; (p', "sweep", c.length)
        | .closeAll => let (p', c) := p.closeAll; (p', "closeAll", c.length)
      p := p'
      stats := stats.insert k (stats.getD k 0 + 1)
      if closed > 0 then stats := stats.insert "(idle connections let go)" (stats.getD "(idle connections let go)" 0 + closed)
    if let some (idx, v) := violation then
      unless quiet do
        IO.println s!"FAIL run {i} (seed {seed}), operation {idx}: {v.property}: {v.detail}"
        IO.println s!"  config: {reprStr config}"
        let small := shrink impl config seq v.property modelCheck
        IO.println s!"  shrunk from {seq.size} to {small.size} operations:"
        for op in small do IO.println s!"    {renderOp op}"
      return some v.property
  unless quiet do
    IO.println s!"PASS {n} runs from seed {seed}: {ops} operations checked"
    for (k, c) in stats.toList.toArray.qsort (·.1 < ·.1) do
      IO.println s!"  {k}: {c}"
  return none

/-! ## Exploration -/

/-- The alphabet: operations over origins a and b, connections 0 to 3, three steps of time. -/
def alphabet (now : Nat) : List (Op × Nat) := Id.run do
  let mut xs := []
  for dt in [0, 5, 10] do
    let t := now + dt
    for o in ["a", "b"] do
      xs := xs ++ [(PoolOp.take o t true, t)]
    xs := xs ++ [(PoolOp.take "a" t false, t), (.sweep t, t)]
    for i in [0, 1, 2, 3] do
      for r in [true, false] do
        xs := xs ++ [(PoolOp.giveBack i r t, t)]
  for i in [0, 1, 2, 3] do
    xs := xs ++ [(PoolOp.drop i, now)]
  return xs ++ [(PoolOp.closeAll, now)]

/-- Breadth-first search to `depth`; returns the states expanded and the first violation. -/
def explore (impl : Impl) (config : PoolConfig) (depth : Nat) (modelCheck : Bool := true) :
    Nat × Option (Array Op × Violation) := Id.run do
  let start : P := Pool.empty config
  let key (p : P) (m : Model) (now : Nat) : String :=
    -- Times relative to now, capped at the timeout: states that differ only by a shift in time
    -- behave alike.  The model is part of the state: with the properties alone, a pool with a bug
    -- planted can drift away from it.
    let rel (t : Nat) := min (now - t) (config.idleTimeoutMs + 1)
    let ms := m.states.toList.map fun
      | .idle o t => s!"i{o}{rel t}" | .out o => s!"o{o}" | .gone => "g"
    s!"{reprStr (p.idle.map fun c => (c.id, c.origin, rel c.since))}|{reprStr p.out}|{p.next}|" ++
      s!"{p.closed}|{ms}|{m.order}|{m.closed}"
  let mut frontier : Array (P × Model × Nat × Array Op) := #[(start, { config }, 0, #[])]
  let mut seen : Std.HashSet String := Std.HashSet.emptyWithCapacity 4096 |>.insert (key start { config } 0)
  let mut expanded := 0
  for _ in [0:depth] do
    let mut next := #[]
    for (p, m, now, path) in frontier do
      expanded := expanded + 1
      for (op, t) in alphabet now do
        -- Connections that do not exist yet are only worth trying just past the next id.
        match op with
        | .giveBack i .. | .drop i => if i > p.next then continue
        | _ => pure ()
        match checkOp impl p m op modelCheck with
        | .error v => return (expanded, some (path.push op, v))
        | .ok (p', m') =>
          let k := key p' m' t
          if !seen.contains k then
            seen := seen.insert k
            next := next.push (p', m', t, path.push op)
    frontier := next
  return (expanded + frontier.size, none)

def searches : List (String × PoolConfig) := [
  ("maxIdle 1, timeout 5, no active cap", { maxIdle := 1, idleTimeoutMs := 5 }),
  ("maxIdle 2, timeout 10, active cap 2", { maxIdle := 2, idleTimeoutMs := 10, maxActive := some 2 }),
  ("maxIdle 0, timeout 10, active cap 1", { maxIdle := 0, idleTimeoutMs := 10, maxActive := some 1 })
]

def runExplore (impl : Impl) (depth : Nat) (quiet : Bool := false) (modelCheck : Bool := true) :
    IO (Option String) := do
  for (name, config) in searches do
    let (n, failure) := explore impl config depth modelCheck
    match failure with
    | some (path, v) =>
      unless quiet do
        IO.println s!"FAIL {name}, depth {depth}: {v.property}: {v.detail}"
        for op in path do IO.println s!"    {renderOp op}"
      return some v.property
    | none => unless quiet do IO.println s!"PASS {name}: {n} states to depth {depth}"
  return none

end PoolTests

open PoolTests

/-! ## Main -/

def main (args : List String) : IO UInt32 := do
  let plantOf (s : Option String) : IO (Option Plant) := do
    match s with
    | none => return none
    | some s =>
      match Plant.parse? s with
      | some p => return some p
      | none => throw (.userError s!"unknown plant {s}; one of {Plant.all.map (·.name)}")
  match args with
  | ["traces"] => runTraces
  | "props" :: n :: seed :: rest =>
    let plant ← plantOf rest.head?
    let r ← runProps (Impl.ofPlant plant) n.toNat! seed.toNat!
    return if r.isNone then 0 else 1
  | "explore" :: depth :: rest =>
    let plant ← plantOf rest.head?
    let r ← runExplore (Impl.ofPlant plant) depth.toNat!
    return if r.isNone then 0 else 1
  | ["control", n, seed, depth] =>
    -- Every plant must be caught, by the random runs and by the exploration.
    -- Each is run twice: with every check, and with the properties alone (no comparison with the
    -- model), to show that the properties catch it on their own.
    let mut missed := 0
    for plant in Plant.all do
      let impl := Impl.ofPlant (some plant)
      for modelCheck in [true, false] do
        let byProps ← runProps impl n.toNat! seed.toNat! (quiet := true) (modelCheck := modelCheck)
        let byExplore ← runExplore impl depth.toNat! (quiet := true) (modelCheck := modelCheck)
        let describe (r : Option String) := r.getD "NOT CAUGHT"
        let mode := if modelCheck then "all checks" else "properties alone"
        IO.println s!"{plant.name}, {mode}: random runs: {describe byProps}; exploration: {describe byExplore}"
        if byProps.isNone || byExplore.isNone then missed := missed + 1
    -- And the real pool must pass the same runs.
    let clean ← runProps {} n.toNat! seed.toNat! (quiet := true)
    let cleanExplore ← runExplore {} depth.toNat! (quiet := true)
    IO.println s!"no plant: random runs: {clean.getD "pass"}; exploration: {cleanExplore.getD "pass"}"
    IO.println s!"{Plant.all.length} plants, {missed} runs that did not catch theirs"
    return if missed == 0 && clean.isNone && cleanExplore.isNone then 0 else 1
  | _ =>
    IO.eprintln "usage: pool-tests traces | props <runs> <seed> [plant] | explore <depth> [plant] | control <runs> <seed> <depth>"
    return 2
