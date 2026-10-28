import Tests.Support.Check

/-!
# Random event sequences

A seeded generator of event sequences that an environment could plausibly produce: the shell
completes the operations the core started, the server sends a scripted response (only once the
request head is written, and for most scripts only once the whole request is), the caller asks for
body or abandons it, and time passes, often straight to the next deadline.  With a small probability
the server also sends bytes when no response can be due, which a real server can do.

Every step is checked (`checkStep`); a failing sequence is shrunk by deleting events while the same
property still fails.
-/

open Std.Http LeanHttp

/-- SplitMix64. -/
structure Rng where
  /-- The state. -/
  state : UInt64

/-- The next number and state. -/
def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.state + 0x9e3779b97f4a7c15
  let z := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- Computations that draw random numbers. -/
abbrev Gen := StateM Rng

/-- A number in `[0, n)`, or 0 if `n` is 0. -/
def below (n : Nat) : Gen Nat := do
  if n == 0 then return 0
  let (x, r) := (← get).next
  set r
  return x.toNat % n

/-- One of `xs`. -/
def pick {α : Type} [Inhabited α] (xs : List α) : Gen α := do
  return xs[← below xs.length]!

/-- One of `xs`, with weights. -/
def pickWeighted {α : Type} [Inhabited α] (xs : List (Nat × α)) : Gen α := do
  let total := xs.foldl (· + ·.1) 0
  let mut k ← below total
  for (w, x) in xs do
    if k < w then return x
    k := k - w
  return default

/-- A response the environment sends, with what the checker knows about it. -/
structure Script where
  /-- A short name. -/
  name : String
  /-- Whether it answers a HEAD request (otherwise GET or POST). -/
  forHead : Bool := false
  /-- The bytes the server sends. -/
  bytes : ByteArray
  /-- Whether the server closes after sending them. -/
  closeAfter : Bool
  /-- Whether the server may answer before the request has been written in full. -/
  early : Bool := false
  /-- The checker's knowledge. -/
  oracle : Oracle

instance : Inhabited Script := ⟨{ name := "", bytes := .empty, closeAfter := false, oracle := {} }⟩

/--
A script whose first `firstLen` bytes are one complete response with body `body` and certain
framing; it permits reuse when `reusable`.
-/
def fixedScript (name : String) (bytes : String) (firstLen : Nat) (body : String)
    (reusable : Bool) (closeAfter : Bool) (forHead early : Bool := false) : Script :=
  let raw := bytes.toUTF8
  let first := raw.extract 0 firstLen
  { name, forHead, bytes := raw, closeAfter, early
    oracle := {
      exactReusable := fun fed => reusable && fed == first
      bodyFor := fun fed => if first.isPrefixOf fed then some body.toUTF8 else none
      body := some body.toUTF8 } }

/-- A script that is one complete response, all of `bytes`. -/
def wholeScript (name : String) (bytes : String) (body : String) (reusable closeAfter : Bool)
    (forHead early : Bool := false) : Script :=
  fixedScript name bytes bytes.utf8ByteSize body reusable closeAfter forHead early

/-- A script whose body runs until the server closes, after a head of `headLen` bytes. -/
def untilCloseScript (name : String) (bytes : String) (headLen : Nat) : Script :=
  let raw := bytes.toUTF8
  { name, bytes := raw, closeAfter := true
    oracle := {
      bodyFor := fun fed => if fed.size ≥ headLen then some (fed.extract headLen fed.size) else none
      body := some (raw.extract headLen raw.size)
      needsEnd := true } }

/-- A script that must never finish: invalid or incomplete. -/
def invalidScript (name : String) (bytes : String) (closeAfter : Bool := true) : Script :=
  { name, bytes := bytes.toUTF8, closeAfter, oracle := {} }

/-- The complete `Content-Length` response most scripts build on. -/
def clHello : String := "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello"

/-- The scripts. -/
def scripts : Array Script := #[
  wholeScript "content-length" clHello "hello" true false,
  wholeScript "content-length, Connection: close"
    "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length: 5\r\n\r\nhello" "hello" false true,
  wholeScript "chunked"
    "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n6\r\n world\r\n0\r\n\r\n"
    "hello world" true false,
  wholeScript "chunked, extensions and trailers"
    "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5;a=1\r\nhello\r\n0\r\nX-T: 1\r\n\r\n"
    "hello" true false,
  untilCloseScript "close-delimited" "HTTP/1.1 200 OK\r\n\r\nabcdef" 19,
  fixedScript "two responses" (clHello ++ "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nno")
    clHello.utf8ByteSize "hello" true false,
  wholeScript "interim responses, then the final one"
    ("HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 103 Early Hints\r\nLink: </a>\r\n\r\n" ++ clHello)
    "hello" true false,
  wholeScript "early 413" "HTTP/1.1 413 Payload Too Large\r\nContent-Length: 3\r\n\r\nbig" "big"
    true false (early := true),
  wholeScript "early 413, then close"
    "HTTP/1.1 413 Payload Too Large\r\nConnection: close\r\nContent-Length: 3\r\n\r\nbig" "big"
    false true (early := true),
  invalidScript "not HTTP" "SSH-2.0-OpenSSH_9.6\r\n",
  invalidScript "truncated body" "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\nhello",
  wholeScript "HTTP/1.0" "HTTP/1.0 200 OK\r\nContent-Length: 2\r\n\r\nok" "ok" false true,
  wholeScript "300-byte body"
    ("HTTP/1.1 200 OK\r\nContent-Length: 300\r\n\r\n" ++ String.ofList (List.replicate 300 'y'))
    (String.ofList (List.replicate 300 'y')) true false,
  wholeScript "204 with Content-Length" "HTTP/1.1 204 No Content\r\nContent-Length: 5\r\n\r\n" ""
    true false,
  invalidScript "101 without upgrade"
    "HTTP/1.1 101 Switching Protocols\r\nUpgrade: x\r\nConnection: upgrade\r\n\r\n",
  invalidScript "conflicting Content-Length"
    "HTTP/1.1 200 OK\r\nContent-Length: 2\r\nContent-Length: 3\r\n\r\nokk",
  wholeScript "HEAD, Content-Length" "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\n" "" true false
    (forHead := true),
  fixedScript "HEAD, then stray bytes" "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello" 38 ""
    true false (forHead := true),
  wholeScript "HEAD, chunked" "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n" "" true false
    (forHead := true)
]

/-- The fixed parameters of one run. -/
structure Case where
  /-- Index into `scripts`. -/
  script : Nat
  /-- The request method. -/
  method : Method
  /-- The request body size. -/
  bodySize : Nat
  /-- The exchange's settings. -/
  config : ExchangeConfig
  /-- The deadline; the exchange begins at time 0. -/
  deadline : Nat

instance : Inhabited Case := ⟨{ script := 0, method := .get, bodySize := 0, config := {}, deadline := 0 }⟩

/-- A short description of a case. -/
def Case.describe (c : Case) : String :=
  let k := c.config
  s!"script={repr scripts[c.script]!.name} method={c.method} body={c.bodySize} keepAlive={k.keepAlive} " ++
    s!"writeChunk={k.writeChunk} gap={k.gapMs} drainBytes={k.drainBytes} drainMs={k.drainMs} " ++
    s!"maxBody={k.maxBody} maxInterim={k.maxInterim} deadline={c.deadline}"

/-- The request of a case. -/
def Case.head (c : Case) : Request.Head :=
  { method := c.method, version := .v11, uri := .originForm { segments := #[], absolute := true } none,
    headers := Headers.empty.insert Header.Name.host (.mk "example.test") }

/-- The prepared request of a case. -/
def Case.prepare (c : Case) : Except Cause PreparedRequest :=
  Exchange.prepare c.config c.head (ByteArray.mk (Array.replicate c.bodySize 'x'.toUInt8))

/-- For drawing positive numbers with `pick`. -/
instance : Inhabited { n : Nat // 0 < n } := ⟨⟨1, by decide⟩⟩

/-- A random case. -/
def genCase : Gen Case := do
  let script ← below scripts.size
  let s := scripts[script]!
  let method ← if s.forHead then pure .head else pick [Method.get, .post]
  let bodySize ← if method == .post then pick [0, 10, 100, 300] else pure 0
  -- Drawn in the order of the fields, as before the gap carried a proof of positivity.
  let keepAlive := (← below 3) < 2
  let writeChunk ← pick [16, 64, 65536]
  let gap ← pick ([⟨50, by decide⟩, ⟨200, by decide⟩, ⟨1000, by decide⟩] : List { n : Nat // 0 < n })
  let config : ExchangeConfig := {
    keepAlive, writeChunk
    gapMs := gap.1
    gapMs_pos := gap.2
    drainBytes := ← pick [0, 4, 64]
    drainMs := ← pick [10, 50]
    maxBody := ← pick [3, 100, 1024]
    maxInterim := ← pick [0, 1, 10] }
  let deadline ← pick [100, 500, 2000]
  return { script, method, bodySize, config, deadline }

/-- What the environment has done so far. -/
structure Env where
  /-- The time. -/
  now : Nat := 0
  /-- Response bytes sent. -/
  sent : Nat := 0
  /-- Whether the server closed. -/
  closed : Bool := false
  /-- Whether bytes were sent when no response could be due. -/
  adversarial : Bool := false
deriving Inhabited

/-- The next event, given the core's state and the checker's model. -/
def genEvent (c : Case) (ex : Exchange) (m : Model) (env : Env) : Gen (Nat × ExchangeEvent × Env) := do
  let s := scripts[c.script]!
  let remaining := s.bytes.size - env.sent
  let chunk : Gen (ExchangeEvent × Env) := do
    let k ← pickWeighted [(3, 1 + (← below (min remaining 8))), (2, remaining),
      (2, 1 + (← below remaining))]
    let k := max 1 (min k remaining)
    return (.received (s.bytes.extract env.sent (env.sent + k)), { env with sent := env.sent + k })
  let mut options : List (Nat × Gen (ExchangeEvent × Env)) := []
  if let some len := m.outstanding then
    options := options ++ [(32, pure (.written len, env)), (2, pure (.writeFailed "reset", env))]
    if len > 1 then
      options := options ++ [(4, do return (.written (← below len), env))]
  if m.readOutstanding && !env.closed then
    let mayAnswer := m.acked ≥ m.headBytes && (s.early || m.acked == m.request.size)
    if mayAnswer && remaining > 0 then
      options := options ++ [(40, chunk)]
    if remaining == 0 && s.closeAfter then
      options := options ++ [(24, pure (.endOfInput, { env with closed := true }))]
    options := options ++ [(2, pure (.endOfInput, { env with closed := true })),
      (2, pure (.readFailed "reset", env)), (2, pure (.received .empty, env))]
  if remaining > 0 && !env.closed then
    options := options ++ [(3, do
      let (e, env) ← chunk
      return (e, { env with adversarial := env.adversarial || !m.readOutstanding ||
        m.acked < m.headBytes }))]
  options := options ++ [
    (10, do return (.wantBody (← pick [1, 3, 1000000]), env)),
    (if m.headDelivered then 4 else 1, pure (.abandon, env))]
  let event? ← if options.isEmpty then pure none else some <$> (pickWeighted (options.map fun (w, g) => (w, some g)))
  let tickAt : Gen Nat := do
    let due := ex.nextDeadline.getD env.now
    let t ← pick [env.now + 1, due - 1, due, due, c.deadline, c.deadline + 7]
    return max env.now t
  let useTick ← (do return (← below 8) == 0)
  match event?, useTick with
  | some (some g), false =>
    let (e, env) ← g
    let dt ← pick [0, 0, 1, 5, 20]
    let now := env.now + dt
    return (now, e, { env with now })
  | _, _ =>
    if (← below 50) == 0 then
      return (env.now - min env.now 3, .tick, env)
    let t ← tickAt
    return (t, .tick, { env with now := t })

/-- How one run went. -/
structure RunResult where
  /-- The events, with their times. -/
  events : Array (Nat × ExchangeEvent) := #[]
  /-- The first violation, with the index of the step (0 for `begin`). -/
  violation : Option (Nat × Violation) := none
  /-- The end action. -/
  ended : Option ExchangeAction := none
  /-- Whether bytes were sent when no response could be due. -/
  adversarial : Bool := false
  /-- Whether the final head arrived before the request was written in full. -/
  earlyHead : Bool := false
  /-- Whether the caller abandoned a body that was then drained. -/
  drained : Bool := false
  /-- Steps checked, counting `begin`. -/
  steps : Nat := 0

/-- Checks `begin` like a step whose event changes nothing in the model. -/
def checkBegin (oracle : Oracle) (prepared : PreparedRequest) (deadline : Nat)
    (skip : List String := []) : Exchange × Model × Option Violation :=
  let (ex, actions) := Exchange.begin prepared 0 deadline
  let m := Model.init prepared deadline 0
  let (m, v) := checkStep oracle m ex 0 (.wantBody 0) ex actions skip
  (ex, m, v)

/-- Replays `events` on case `c`, checking every step. -/
def replay (c : Case) (events : Array (Nat × ExchangeEvent)) (skip : List String := []) :
    Option (Nat × Violation) := Id.run do
  let .ok prepared := c.prepare | return some (0, { property := "prepare", detail := "refused" })
  let oracle := scripts[c.script]!.oracle
  let (ex, m, v) := checkBegin oracle prepared c.deadline skip
  if let some v := v then return some (0, v)
  let mut ex := ex
  let mut m := m
  for (i, (now, event)) in events.zipIdx.map (fun (e, i) => (i, e)) do
    let (ex', actions) := ex.step now event
    let (m', v) := checkStep oracle m ex now event ex' actions skip
    if let some v := v then return some (i + 1, v)
    ex := ex'
    m := m'
  return none

/-- Generates and checks one run of case `c`. -/
def genRun (c : Case) (skip : List String := []) (maxSteps : Nat := 80) : Gen RunResult := do
  let .ok prepared := c.prepare
    | return { violation := some (0, { property := "prepare", detail := "refused" }) }
  let oracle := scripts[c.script]!.oracle
  let (ex, m, v) := checkBegin oracle prepared c.deadline skip
  let mut result : RunResult := { steps := 1, violation := v.map (0, ·) }
  if v.isSome then return result
  let mut ex := ex
  let mut m := m
  let mut env : Env := {}
  let mut after := 0
  for _ in [0:maxSteps] do
    if ex.terminal then
      after := after + 1
      if after > 2 then break
    let (now, event, env') ← genEvent c ex m env
    env := env'
    let (ex', actions) := ex.step now event
    let (m', v) := checkStep oracle m ex now event ex' actions skip
    result := { result with events := result.events.push (now, event), steps := result.steps + 1 }
    if let some v := v then
      return { result with violation := some (result.events.size, v), adversarial := env.adversarial }
    if ex.phase matches .receiving && ex'.phase matches .draining then
      result := { result with drained := true }
    for a in actions do
      match a with
      | .deliverHead _ => if ex'.early then result := { result with earlyHead := true }
      | .finish _ | .fail _ => result := { result with ended := some a }
      | _ => pure ()
    ex := ex'
    m := m'
  return { result with adversarial := env.adversarial }

/--
Shrinks a failing sequence: deletes events, one at a time, while the same property still fails.
-/
def shrink (c : Case) (events : Array (Nat × ExchangeEvent)) (property : String)
    (skip : List String := []) : Array (Nat × ExchangeEvent) := Id.run do
  let mut current := events
  let mut changed := true
  while changed do
    changed := false
    let mut i := 0
    while i < current.size do
      let candidate := current.eraseIdx! i
      match replay c candidate skip with
      | some (_, v) =>
        if v.property == property then
          current := candidate
          changed := true
        else
          i := i + 1
      | none => i := i + 1
  return current
