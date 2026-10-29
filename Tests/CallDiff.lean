import LeanHttp.Call
import LeanHttpProto.Http.Protocol.H1.Redirect
import Std.Http.Protocol.H1.Redirect
import Tests.Support.CallCases
import Tests.Support.Gen

/-!
# Differential test of the redirect decisions

Two parts.

1. **One decision.**  Every combination of status (the 3xx codes, an undefined 3xx and 200),
   response version, method, body kind, `Location` (from `locationPool`, or none) and current origin
   (the original one, or another), each with a few random sets of request fields, decided by the
   planner (`Call.decideRedirect`) and by two oracles: the redirect planner of the upstream client
   stack (leanprover/lean4 PR 14548, vendored as `LeanHttpProto`) and the one in the v4.34.1
   toolchain (`Std.Http.Protocol.H1`), the latter with `onlySafeRedirects` off and on.  The results
   are compared as: followed or not, next origin, method, path and query, fields (as a multiset)
   and whether the body goes again.
2. **Chains.**  Random chains of redirects driven through `Call.plan` and through a model of the
   upstream client's redirect loop (`sendWithRedirects` and `evaluateRedirect` at the same commit),
   which delivers the last response when its hop budget is spent or when a target repeats.

Every disagreement must be explained by one of the deliberate differences listed in `classes`: the
known difference is neutralised (the oracle run again with the input changed, or the results
adjusted) and the results must then agree.  A disagreement no class explains fails the test.

Usage: `call-diff [field sets per combination] [seed] [chains]` (defaults: 3, 1, 20000).
-/

open Std.Http LeanHttp LeanHttp.Call

/-- A bug planted in the planner's decision, to show that the comparison sees it. -/
inductive Plant where
  | none
  | leakCredentials
  | keepPostOn303
  | keepHost
deriving BEq, Repr, Inhabited

/-- One redirect decision to compare. -/
structure RCase where
  /-- The response's status code. -/
  code : UInt16
  /-- The response's version. -/
  version : Version
  /-- The current request's method. -/
  method : Method
  /-- The kind of the call's body. -/
  kind : BodyKind
  /-- The response's `Location`, if any. -/
  location : Option String
  /-- Whether the current request goes to the call's original origin, `http://a.test`. -/
  atOriginal : Bool
  /-- The current request's fields. -/
  fields : List (String × String)
  /-- The credential fields of the call's first request. -/
  given : List (String × String)
  /-- Whether the v4.34.1 oracle refuses methods that are not safe (`onlySafeRedirects`). -/
  onlySafe : Bool := false
  /-- Whether the oracle is the v4.34.1 one (rather than the PR head). -/
  fromToolchain : Bool := false
  /-- A bug planted in the planner's result, for the positive control. -/
  plant : Plant := .none

/-- A redirect decision in a form both planners can be brought to. -/
structure Norm where
  /-- Whether the redirect is followed. -/
  follow : Bool
  /-- The next origin. -/
  origin : String := ""
  /-- The next method. -/
  method : String := ""
  /-- The next path and query. -/
  target : String := ""
  /-- The next fields, sorted. -/
  fields : List (String × String) := []
  /-- Whether the next request carries the original (non-empty) body. -/
  carriesBody : Bool := false
deriving BEq, Repr

/-- A decision on one line. -/
def Norm.short (n : Norm) : String :=
  if !n.follow then "not followed" else
  let fields := String.intercalate "; " (n.fields.map fun (k, v) => s!"{k}: {v}")
  s!"{n.method} {n.origin}{n.target} body {if n.carriesBody then "sent again" else "none"} [{fields}]"

/-- The original origin of every case. -/
def originalUri : String := "http://a.test"

/-- The current request's origin. -/
def RCase.current (c : RCase) : String := if c.atOriginal then originalUri else "http://b.test"

/-- The current request's head. -/
def RCase.head (c : RCase) : Request.Head :=
  headOf c.method (c.current ++ "/a/b/c?x=1") c.fields

/-- The response. -/
def RCase.response (c : RCase) : Response.Head :=
  respOf c.code (c.location.map (fun l => [("Location", l)]) |>.getD []) c.version

/-- An origin as a string. -/
def keyString (o : URI.Origin) : String :=
  let k := originKey o
  s!"{k.scheme}://{k.host}:{k.port}"

/-- Sorted fields. -/
def sortedFields (h : Headers) : List (String × String) :=
  (fieldStrings h).mergeSort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)

/-- The origin of a URI string, which must have one. -/
def mustOrigin (uri : String) : URI.Origin :=
  match uriOrigin (URI.parse! uri) with
  | some o => o
  | none => default

/-- The planner's decision. -/
def ours (c : RCase) : Norm :=
  let hop : Hop := { origin := mustOrigin c.current, head := c.head, body := .original }
  let given := (fieldsOf c.given).toList
  let decision := decideRedirect c.kind (mustOrigin originalUri) given hop c.response
  let decision : Decision := match decision, c.plant with
    | .follow next, .leakCredentials =>
      if originKey next.origin != originKey (mustOrigin originalUri) then
        .follow { next with head := { next.head with headers := .ofList (next.head.headers.toList ++ given) } }
      else decision
    | .follow next, .keepPostOn303 =>
      if c.code == 303 && c.method == .post then .follow { next with head := { next.head with method := Method.post } }
      else decision
    | .follow next, .keepHost =>
      let old := c.head.headers.toList.filter (·.1 == Header.Name.host)
      let rest := next.head.headers.toList.filter (·.1 != Header.Name.host)
      if originKey next.origin != originKey hop.origin && !old.isEmpty then
        .follow { next with head := { next.head with headers := .ofList (rest ++ old) } }
      else decision
    | _, _ => decision
  match decision with
  | .follow next => {
      follow := true, origin := keyString next.origin, method := toString next.head.method,
      target := targetPathQuery next.head.uri, fields := sortedFields next.head.headers,
      carriesBody := next.body == .original && c.kind != .none }
  | _ => { follow := false }

/-- A followed redirect of either oracle, in normal form. -/
def oracleNorm (c : RCase) (origin : URI.Origin) (target : RequestTarget) (method : Method)
    (headers : Headers) (replay : Bool) : Norm :=
  { follow := true, origin := keyString origin, method := toString method,
    target := targetPathQuery target, fields := sortedFields headers,
    carriesBody := replay && c.kind != .none }

/-- The vendored planner's decision (upstream PR head). -/
def vendored (c : RCase) : Norm :=
  match LeanHttpProto.Http.Protocol.H1.decideRedirect (mustOrigin c.current) c.head
      c.kind.replayable c.version (statusOf c.code) c.response.headers with
  | .follow p => oracleNorm c p.origin p.target p.method p.headers (p.bodyAction == .replay)
  | .done => { follow := false }

/-- The toolchain planner's decision (v4.34.1), with the case's `onlySafeRedirects`. -/
def toolchain (c : RCase) : Norm :=
  match Std.Http.Protocol.H1.decideRedirect (mustOrigin c.current) c.head c.kind.replayable c.onlySafe
      c.version (statusOf c.code) c.response.headers with
  | .follow p => oracleNorm c p.origin p.target p.method p.headers (p.bodyAction == .replay)
  | .done => { follow := false }

/--
A deliberate difference: when it applies, and how to neutralise it: by changing the case the oracle
decides, the case both decide, or the results.
-/
structure DiffClass where
  /-- What the difference is. -/
  name : String
  /-- Whether it can apply to the case. -/
  applies : RCase → Bool
  /-- Changes the case the oracle decides. -/
  oracleInput : RCase → RCase := id
  /-- Changes the case both decide. -/
  bothInput : RCase → RCase := id
  /-- Adjusts the results (the planner's, the oracle's) of the case. -/
  adjust : RCase → Norm → Norm → Norm × Norm := fun _ m t => (m, t)

/-- The credential field names. -/
def isCredential (n : String) : Bool := credentialNameStrings.contains n

/-- The deliberate differences. -/
def classes : List DiffClass := [
  { name := "undefined 3xx code: the oracles follow any 3xx with a Location (but 300, 304, 305 and 306), the planner only 301, 302, 303, 307 and 308"
    applies := fun c => c.code.toNat > 308 && c.code.toNat < 400
    adjust := fun _ m _ => (m, { follow := false }) },
  { name := "HTTP/1.0 response: the oracles follow only 301 and 302, and keep POST; the planner treats every version alike"
    applies := fun c => c.version == .v10
    oracleInput := fun c => { c with version := .v11 } },
  { name := "301 or 302 with a method other than GET, HEAD and POST: the oracles refuse it, the planner keeps the method, as for 307"
    applies := fun c => (c.code == 301 || c.code == 302) && !([Method.get, .head, .post].contains c.method)
    oracleInput := fun c => { c with code := 307 } },
  { name := "GET or HEAD with a body, on a redirect that keeps the method: the oracles drop the body, the planner sends it again (or refuses a stream)"
    applies := fun c => (c.method == .get || c.method == .head) && c.kind != .none
    bothInput := fun c => { c with kind := .none } },
  { name := "back at the original origin: the planner gives the credentials back"
    applies := fun c => !c.atOriginal
    adjust := fun _ m t =>
      if m.origin == keyString (mustOrigin originalUri) then
        ({ m with fields := m.fields.filter (!isCredential ·.1) }, t)
      else (m, t) },
  { name := "Digest dropped with a method change: the planner drops the digest fields, the oracles keep them"
    applies := fun c => c.fields.any (·.1 == "Digest")
    adjust := fun c m t =>
      if m.follow && m.method != toString c.method then
        let drop (n : Norm) := { n with fields := n.fields.filter (·.1 != "digest") }
        (drop m, drop t)
      else (m, t) },
  { name := "onlySafeRedirects (v4.34.1 only): refuses every method that is not safe; the planner has no such option"
    applies := fun c => c.onlySafe
    oracleInput := fun c => { c with onlySafe := false } },
  { name := "dot segments and empty path of an absolute Location (v4.34.1 only): left as they are; the planner and the PR head resolve them"
    applies := fun c => c.fromToolchain && match c.location with
      | some l => l.startsWith "http" || l.startsWith "HTTP"
      | none => false
    adjust := fun _ m t => if t.follow then (m, { t with target := m.target }) else (m, t) }]

/-- Neutralises the named classes that apply, and returns the two results. -/
def neutraliseAll (oracle : RCase → Norm) (c : RCase) (names : List String) : Norm × Norm :=
  let used := classes.filter fun cls => names.contains cls.name && cls.applies c
  let both := used.foldl (fun c cls => cls.bothInput c) c
  let forOracle := used.foldl (fun c cls => cls.oracleInput c) both
  used.foldl (fun (m, t) cls => cls.adjust c m t) (ours both, oracle forOracle)

/--
Explains a disagreement: a smallest set of classes (found greedily) whose neutralisation makes the
results agree, or `none` when neutralising every class that applies leaves them different.
-/
def explain (oracle : RCase → Norm) (c : RCase) : Option (List String) := Id.run do
  let agrees (names : List String) : Bool :=
    let (m, t) := neutraliseAll oracle c names
    m == t
  let all := (classes.filter (·.applies c)).map (·.name)
  if !agrees all then return none
  let mut used := all
  for n in all do
    let without := used.filter (· != n)
    if agrees without then used := without
  return some used

/-- The results of comparing with one oracle. -/
structure DiffStats where
  /-- Decisions compared. -/
  cases : Nat := 0
  /-- Decisions where the planner follows. -/
  followed : Nat := 0
  /-- Decisions that agree. -/
  agree : Nat := 0
  /-- Disagreements by explanation, with a count and an example. -/
  explained : List (List String × Nat × String) := []
  /-- Unexplained disagreements, with an example each. -/
  unexplained : List String := []

/-- A case, briefly. -/
def RCase.describe (c : RCase) : String :=
  s!"{c.code} HTTP/{if c.version == .v10 then "1.0" else "1.1"} {c.method} body {repr c.kind} \
    Location {c.location} from {c.current} fields {c.fields}"

/-- Records a comparison. -/
def DiffStats.add (s : DiffStats) (oracle : RCase → Norm) (c : RCase) : DiffStats :=
  let mine := ours c
  let theirs := oracle c
  let s := { s with cases := s.cases + 1, followed := s.followed + (if mine.follow then 1 else 0) }
  if mine == theirs then { s with agree := s.agree + 1 } else
  match explain oracle c with
  | some why =>
    match s.explained.find? (·.1 == why) with
    | some _ => { s with explained := s.explained.map fun (w, n, e) => if w == why then (w, n + 1, e) else (w, n, e) }
    | none => { s with explained := s.explained ++ [(why, 1,
        s!"{c.describe}\n        planner: {mine.short}\n        oracle:  {theirs.short}")] }
  | none =>
    if s.unexplained.length < 5 then
      { s with unexplained := s.unexplained ++ [s!"{c.describe}\n        planner: {mine.short}\n        oracle:  {theirs.short}"] }
    else { s with unexplained := s.unexplained ++ [""] }

/-- The codes compared. -/
def codes : List UInt16 := [200, 300, 301, 302, 303, 304, 305, 306, 307, 308, 399]

/-- A random set of fields for a current request, and the credentials of the first request. -/
def genFields (atOriginal : Bool) : Gen (List (String × String) × List (String × String)) := do
  let mut fields : List (String × String) := []
  let mut creds : List (String × String) := []
  for f in credentialPool do
    if (← below 2) == 0 then creds := creds ++ [f]
  if atOriginal then fields := fields ++ creds
  for f in otherFieldPool do
    if (← below 3) == 0 then fields := fields ++ [f]
  if (← below 2) == 0 then fields := fields ++ [("Host", if atOriginal then "a.test" else "b.test")]
  return (fields, creds)

/-- Every case, with `k` random field sets each. -/
def allCases (k : Nat) (seed : UInt64) : Array RCase := Id.run do
  let mut rng : Rng := ⟨seed⟩
  let mut out := #[]
  for code in codes do
    for version in [Version.v11, .v10] do
      for method in methodPool do
        for kind in bodyKindPool do
          for location in (locationPool.map some) ++ [none] do
            for atOriginal in [true, false] do
              for _ in [0:k] do
                let ((fields, given), r) := (genFields atOriginal).run rng
                rng := r
                out := out.push { code, version, method, kind, location, atOriginal, fields, given }
  return out

/-- Prints the comparison with one oracle and returns whether every disagreement is explained. -/
def report (name : String) (oracle : RCase → Norm) (cases : Array RCase) : IO Nat := do
  let s := cases.foldl (fun (s : DiffStats) c => s.add oracle c) {}
  IO.println s!"== {name}: {s.cases} decisions, {s.followed} followed by the planner, {s.agree} agree, \
    {s.cases - s.agree} disagree"
  let explainedCount := s.explained.foldl (· + ·.2.1) 0
  IO.println s!"  {explainedCount} explained, by {s.explained.length} combinations of these differences:"
  for cls in classes do
    let total : Nat := s.explained.foldl (fun n (why, k, _) => if why.contains cls.name then n + k else n) 0
    if total > 0 then
      let alone := s.explained.find? (·.1 == [cls.name])
      IO.println s!"  - {cls.name}"
      IO.println s!"      in {total} disagreements, alone in {(alone.map (·.2.1)).getD 0}"
      if let some (_, _, sample) := alone then IO.println s!"      e.g. {sample}"
  IO.println s!"  {s.unexplained.length} unexplained"
  for e in s.unexplained.filter (· != "") do
    IO.println s!"      {e}"
  return s.unexplained.length

/-! ## Chains -/

/-- What one step of a chain did, as both sides can say it. -/
inductive ChainStep where
  | follow (origin : String) (method : String) (target : String)
  | deliver
  | fail
deriving BEq, Repr, Inhabited

/-- Why the upstream loop delivered. -/
inductive UpstreamWhy where
  | budget
  | revisit
  | done
deriving BEq, Repr

/-- The cycle-detection key of the upstream client: path and query only. -/
def targetKey (t : RequestTarget) : String := targetPathQuery t

/--
The upstream client's redirect loop over a chain of responses (`sendWithRedirects` with
`evaluateRedirect`, PR 14548 at 3e6f42a): each step returns what it did, and why it delivered.
-/
def upstreamChain (maxRedirects : Nat) (head : Request.Head) (kind : BodyKind)
    (responses : List Response.Head) : List (ChainStep × Option UpstreamWhy) := Id.run do
  let mut origin := mustOrigin (match head.uri with
    | .absoluteForm u => toString u
    | _ => "")
  let mut req := head
  let mut remaining := maxRedirects
  let mut history : Array (String × String) := #[]
  let mut out := []
  for resp in responses do
    history := history.push (keyString origin, targetKey req.uri)
    if remaining == 0 then return out ++ [(.deliver, some .budget)]
    match LeanHttpProto.Http.Protocol.H1.decideRedirect origin req kind.replayable resp.version
        resp.status resp.headers with
    | .done => return out ++ [(.deliver, some .done)]
    | .follow p =>
      if history.contains (keyString p.origin, targetKey p.target) then
        return out ++ [(.deliver, some .revisit)]
      out := out ++ [(.follow (keyString p.origin) (toString p.method) (targetKey p.target), none)]
      origin := p.origin
      req := { req with method := p.method, uri := p.target, headers := p.headers }
      remaining := remaining - 1
  return out

/-- The planner over the same chain. -/
def plannerChain (maxRedirects : Nat) (head : Request.Head) (kind : BodyKind)
    (responses : List Response.Head) : List ChainStep := Id.run do
  let some st0 := (start { maxRedirects } head kind 0 1000000).toOption | return [.fail]
  let mut st := st0
  let mut out := []
  for resp in responses do
    let (st', step) := plan st { now := 0, wallSec := 784111777 } (.response resp)
    st := st'
    match step with
    | .follow next =>
      out := out ++ [.follow (keyString next.origin) (toString next.head.method) (targetPathQuery next.head.uri)]
    | .deliver => return out ++ [.deliver]
    | _ => return out ++ [.fail]
  return out

/-- Compares random chains; returns whether every difference is explained. -/
def chainReport (n : Nat) (seed : UInt64) : IO Bool := do
  let mut rng : Rng := ⟨seed⟩
  let mut agree := 0
  let mut limit := 0
  let mut revisit := 0
  let mut unexplained : List String := []
  let mut longest := 0
  for _ in [0:n] do
    let gen : Gen (Nat × Request.Head × BodyKind × List Response.Head) := do
      let max ← pick [0, 1, 2, 3, 10]
      let (method, kind) ← pick [(Method.get, BodyKind.none), (.post, .bytes)]
      let len ← below 15
      let mut resps := []
      for _ in [0:len] do
        let code ← pick ([301, 302, 303, 307, 308] : List UInt16)
        let loc ← pick ["/items", "/a", "/b", "http://b.test/items", "http://a.test/items", "/items?x=1"]
        resps := resps ++ [redirectTo code loc]
      return (max, headOf method "http://a.test/items", kind, resps)
    let ((max, head, kind, resps), r) := gen.run rng
    rng := r
    let up := upstreamChain max head kind resps
    let mine := plannerChain max head kind resps
    let upSteps := up.map (·.1)
    if upSteps == mine then
      agree := agree + 1
      longest := Nat.max longest mine.length
    else
      -- The first difference must be one of the two deliberate ones.
      let i := (List.range (Nat.min upSteps.length mine.length)).find? (fun i => upSteps[i]! != mine[i]!)
      let i := i.getD (Nat.min upSteps.length mine.length)
      match up[i]?, mine[i]? with
      | some (.deliver, some .budget), some .fail => limit := limit + 1
      | some (.deliver, some .revisit), some (.follow ..) => revisit := revisit + 1
      | u, m =>
        if unexplained.length < 5 then
          unexplained := unexplained ++ [s!"max {max} {head.method}: upstream {repr u}, planner {repr m}"]
        else unexplained := unexplained ++ [""]
  IO.println s!"== chains against the upstream client's loop: {n} chains, {agree} agree \
    (longest {longest} steps), {n - agree} differ"
  IO.println s!"  {limit} explained by: hop limit: the upstream loop delivers the last 3xx when its budget is spent, the planner fails with tooManyRedirects"
  IO.println s!"  {revisit} explained by: no cycle detection: the upstream loop delivers a 3xx whose target (origin, path and query, not method) was visited, the planner follows it"
  IO.println s!"  {unexplained.length} unexplained"
  for e in unexplained.filter (· != "") do
    IO.println s!"      {e}"
  return unexplained.isEmpty && limit > 0 && revisit > 0

def main (args : List String) : IO UInt32 := do
  let k := (args[0]?.bind String.toNat?).getD 3
  let seed := ((args[1]?.bind String.toNat?).getD 1).toUInt64
  let n := (args[2]?.bind String.toNat?).getD 20000
  let cases := allCases k seed
  let a ← report "upstream PR head (vendored)" vendored cases
  let b ← report "v4.34.1 toolchain, onlySafeRedirects false" toolchain
    (cases.map fun c => { c with fromToolchain := true })
  let c ← report "v4.34.1 toolchain, onlySafeRedirects true" toolchain
    (cases.map fun c => { c with fromToolchain := true, onlySafe := true })
  let d ← chainReport n seed
  -- Positive controls: the same comparison with a bug planted in the planner must find it.
  let mut controls := true
  for plant in [Plant.leakCredentials, .keepPostOn303, .keepHost] do
    let u ← report s!"control: upstream PR head, planner with {repr plant} planted" vendored
      (cases.map fun c => { c with plant })
    if u == 0 then controls := false
  IO.println (if controls then "every planted bug found" else "A PLANTED BUG WAS NOT FOUND")
  let ok := a == 0 && b == 0 && c == 0 && d && controls
  IO.println (if ok then "every disagreement explained" else "UNEXPLAINED DISAGREEMENTS")
  return if ok then 0 else 1
