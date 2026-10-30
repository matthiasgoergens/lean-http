import Tests.Support.Gen

/-!
# Bounded exhaustive exploration

Breadth-first search over every sequence of events from a small alphabet, to a fixed depth, with the
same checks at every step as the random runs.  States are de-duplicated by a fingerprint of the core
(its phase, counters, timers and the machine's reader state and input position) together with the
checker's model and the environment, so each distinct state is expanded once.

The alphabet: complete the write in flight (in full, or one byte of it), fail it; send the next piece
of the scripted response or all the rest (once the request head is written and a read is in flight),
end the input, fail the read; send the next piece when no response can be due; ask for one byte of
body or for all of it; abandon; tick just before the next deadline, at it, or after the deadline of
the exchange.  Only ticks move time, so the space is finite.
-/

open Std.Http LeanHttp

/-- One letter of the alphabet. -/
inductive Letter where
  /-- The write in flight completes in full. -/
  | writeAll
  /-- One byte of the write in flight is accepted. -/
  | writeOne
  /-- The write in flight fails. -/
  | writeFail
  /-- The next piece of the response arrives. -/
  | piece
  /-- The rest of the response arrives. -/
  | rest
  /-- The input ends. -/
  | eof
  /-- The read in flight fails. -/
  | readFail
  /-- The next piece arrives although no response can be due. -/
  | unsolicited
  /-- The caller wants one more body byte. -/
  | wantOne
  /-- The caller wants the whole body. -/
  | wantLots
  /-- The caller abandons. -/
  | abandon
  /-- A tick just before the next deadline. -/
  | tickBefore
  /-- A tick at the next deadline. -/
  | tickDue
  /-- A tick after the exchange's deadline. -/
  | tickLate
  /-- The producer answers the pull in flight as its plan says. -/
  | pullNext
  /-- The producer fails the pull in flight. -/
  | pullFail
deriving Repr, Inhabited

/-- Every letter. -/
def alphabet : List Letter :=
  [.writeAll, .writeOne, .writeFail, .piece, .rest, .eof, .readFail, .unsolicited, .wantOne,
    .wantLots, .abandon, .tickBefore, .tickDue, .tickLate, .pullNext, .pullFail]

/-- One search: a case, and where its response is cut into pieces. -/
structure Search where
  /-- What the search covers. -/
  name : String
  /-- The case. -/
  case : Case
  /-- The offsets where `piece` stops, in increasing order; the last piece runs to the end. -/
  cuts : List Nat

/-- A state of the search. -/
structure Node where
  /-- The core. -/
  ex : Exchange
  /-- The checker's model. -/
  model : Model
  /-- The environment. -/
  env : Env
  /-- The events that led here. -/
  path : Array (Nat × ExchangeEvent)

/-- The event a letter stands for in a state, if the environment can produce it there. -/
def letterEvent (s : Search) (n : Node) : Letter → Option (Nat × ExchangeEvent × Env)
  | .writeAll => n.model.outstanding.map fun len => (n.env.now, .written len, n.env)
  | .writeOne => n.model.outstanding.bind fun len =>
      if len > 1 then some (n.env.now, .written 1, n.env) else none
  | .writeFail => n.model.outstanding.map fun _ => (n.env.now, .writeFailed "reset", n.env)
  | .piece => if plausible then send pieceSize else none
  | .rest => if plausible then send remaining else none
  | .eof =>
    if n.model.readOutstanding && !n.env.closed then
      some (n.env.now, .endOfInput, { n.env with closed := true })
    else none
  | .readFail =>
    if n.model.readOutstanding && !n.env.closed then some (n.env.now, .readFailed "reset", n.env)
    else none
  | .unsolicited => if !plausible && remaining > 0 && !n.env.closed then send pieceSize else none
  | .wantOne => some (n.env.now, .wantBody 1, n.env)
  | .wantLots => some (n.env.now, .wantBody 1000000, n.env)
  | .abandon => some (n.env.now, .abandon, n.env)
  | .tickBefore => n.ex.nextDeadline.bind fun due =>
      if due > n.env.now + 1 then some (due - 1, .tick, { n.env with now := due - 1 }) else none
  | .tickDue => n.ex.nextDeadline.map fun due =>
      let t := max due n.env.now
      (t, .tick, { n.env with now := t })
  | .tickLate =>
    let t := s.case.deadline + 1
    if t > n.env.now then some (t, .tick, { n.env with now := t }) else none
  | .pullNext => s.case.stream.bind fun p =>
    if n.model.pullOutstanding then
      some (n.env.now, p.answer n.env.pulls, { n.env with pulls := n.env.pulls + 1 })
    else none
  | .pullFail =>
    if n.model.pullOutstanding then
      some (n.env.now, .pullFailed "the producer failed", { n.env with pulls := n.env.pulls + 1 })
    else none
where
  script := scripts[s.case.script]!
  remaining := script.bytes.size - n.env.sent
  pieceSize := ((s.cuts.find? (· > n.env.sent)).getD script.bytes.size |> min script.bytes.size) - n.env.sent
  plausible := n.model.readOutstanding && !n.env.closed && remaining > 0 &&
    n.model.acked ≥ n.model.headBytes
  send (k : Nat) : Option (Nat × ExchangeEvent × Env) :=
    if k == 0 then none else
    some (n.env.now, .received (script.bytes.extract n.env.sent (n.env.sent + k)),
      { n.env with sent := n.env.sent + k })

/-- The de-duplication key of a state. -/
def Node.key (n : Node) : String :=
  let m := n.model
  s!"{fingerprint n.ex}#{m.acked}|{m.outstanding}|{m.everWrote}|{m.readOutstanding}|" ++
    s!"{m.headDelivered}|{m.ackedAtHead}|{m.fed.size}|{m.unsolicited}|{m.eofSeen}|{m.abandoned}|" ++
    s!"{m.ended}|{m.body.size}|{m.now}#{n.env.sent}|{n.env.closed}|{n.env.now}" ++
    s!"|{m.request.size}|{m.complete}|{m.pullOutstanding}|{m.everPulled}|{m.bodyBroken}|{n.env.pulls}"

/-- What a search found. -/
structure SearchResult where
  /-- Distinct states reached, counting the start. -/
  states : Nat := 0
  /-- Steps checked. -/
  transitions : Nat := 0
  /-- Distinct states at each depth. -/
  perDepth : Array Nat := #[]
  /-- Distinct terminal states reached. -/
  terminals : Nat := 0
  /-- Of those, how many finished with a reusable connection. -/
  reusableEnds : Nat := 0
  /-- The first violation, with the events that led to it. -/
  violation : Option (Array (Nat × ExchangeEvent) × Violation) := none

/-- Searches every sequence of letters up to `depth`. -/
def explore (s : Search) (depth : Nat) (skip : List String := []) : SearchResult := Id.run do
  let .ok prepared := s.case.prepare
    | return { violation := some (#[], { property := "prepare", detail := "refused" }) }
  let oracle := scripts[s.case.script]!.oracle
  let (ex, m, v) := checkBegin oracle prepared s.case.deadline skip
  if let some v := v then return { violation := some (#[], v) }
  let start : Node := { ex, model := m, env := {}, path := #[] }
  let mut seen : Std.HashSet String := Std.HashSet.emptyWithCapacity 4096 |>.insert start.key
  let mut frontier := #[start]
  let mut result : SearchResult := { states := 1, perDepth := #[1] }
  for _ in [0:depth] do
    let mut next := #[]
    for n in frontier do
      for letter in alphabet do
        let some (now, event, env) := letterEvent s n letter | continue
        let (ex', actions) := n.ex.step now event
        let (m', v) := checkStep oracle n.model n.ex now event ex' actions skip
        result := { result with transitions := result.transitions + 1 }
        let path := n.path.push (now, event)
        if let some v := v then
          return { result with violation := some (path, v) }
        let node : Node := { ex := ex', model := m', env, path }
        let key := node.key
        if !seen.contains key then
          seen := seen.insert key
          result := { result with states := result.states + 1 }
          if ex'.terminal then
            result := { result with terminals := result.terminals + 1 }
            if ex'.phase matches .finished true then
              result := { result with reusableEnds := result.reusableEnds + 1 }
          else
            next := next.push node
    result := { result with perDepth := result.perDepth.push next.size }
    frontier := next
  return result

/-- The index of the script named `name`. -/
def scriptIndex (name : String) : Nat :=
  (scripts.findIdx? (·.name == name)).getD 0

/-- The searches.  The cuts put a piece boundary at the end of each complete response. -/
def searches : List Search :=
  let base : ExchangeConfig := { keepAlive := true, gapMs := 100, drainMs := 50, maxBody := 1024 }
  let get (script : String) (cuts : List Nat) (config : ExchangeConfig := base) : Search :=
    { name := s!"GET, {script}, keepAlive={config.keepAlive}"
      case := { script := scriptIndex script, method := .get, bodySize := 0, config, deadline := 300 }
      cuts }
  -- `clHello` is 43 bytes: a 38-byte head and a 5-byte body.
  [ get "content-length" [20, 38],
    get "content-length" [20, 38] { base with keepAlive := false },
    get "two responses" [20, 38, 43, 60],
    get "interim responses, then the final one" [25, 65, 90],
    get "chunked" [47, 57, 68] { base with drainBytes := 4 },
    get "close-delimited" [19],
    get "not HTTP" [10],
    get "truncated body" [20, 38],
    get "content-length, Connection: close" [30],
    { name := "HEAD, then stray bytes, keepAlive=true"
      case := { script := scriptIndex "HEAD, then stray bytes", method := .head, bodySize := 0,
                config := base, deadline := 300 }
      cuts := [20, 38] },
    { name := "POST of 20 bytes in 32-byte writes, early 413, keepAlive=true"
      case := { script := scriptIndex "early 413", method := .post, bodySize := 20,
                config := { base with writeChunk := 32 }, deadline := 300 }
      cuts := [20, 53] },
    { name := "POST streamed chunked in chunks of 3 and 4 bytes, content-length, keepAlive=true"
      case := { script := scriptIndex "content-length", method := .post, bodySize := 0,
                config := base, deadline := 300,
                stream := some { declared := none, chunks := [3, 4] } }
      cuts := [20, 38] },
    { name := "POST streamed with 7 bytes declared, 3 and 4 given in 32-byte writes, early 413"
      case := { script := scriptIndex "early 413", method := .post, bodySize := 0,
                config := { base with writeChunk := 32 }, deadline := 300,
                stream := some { declared := some 7, chunks := [3, 4] } }
      cuts := [20, 53] },
    { name := "POST streamed with 5 bytes declared and 7 given, content-length"
      case := { script := scriptIndex "content-length", method := .post, bodySize := 0,
                config := base, deadline := 300,
                stream := some { declared := some 5, chunks := [3, 4] } }
      cuts := [20, 38] } ]
