import LeanHttp.Exchange

/-!
# Driving the exchange core in tests

A pure stand-in for the shell: applies events to the exchange core and records what its actions
delivered, so that tests can feed a response and look at the outcome.
-/

open Std.Http LeanHttp

/-- An exchange and everything its actions delivered so far. -/
structure Run where
  /-- The exchange. -/
  ex : Exchange
  /-- The final response head, once delivered. -/
  head : Option Response.Head := none
  /-- The body delivered so far. -/
  body : ByteArray := .empty
  /-- The `finish` or `fail` action, once emitted. -/
  ended : Option ExchangeAction := none
  /-- Every action, in order. -/
  actions : Array ExchangeAction := #[]

namespace Run

/-- Records one action. -/
def record (r : Run) (action : ExchangeAction) : Run :=
  let r := { r with actions := r.actions.push action }
  match action with
  | .deliverHead head => { r with head := some head }
  | .deliverBody bytes => { r with body := r.body ++ bytes }
  | .finish _ | .fail _ => { r with ended := some action }
  | _ => r

/-- Applies one event at time `now`. -/
def apply (r : Run) (now : Timestamp) (event : ExchangeEvent) : Run :=
  let (ex, actions) := r.ex.step now event
  actions.foldl record { r with ex }

/-- Begins `prepared` at time 0 with a distant deadline. -/
def begin (prepared : PreparedRequest) (deadline : Timestamp := 1000000000) : Run :=
  let (ex, actions) := Exchange.begin prepared 0 deadline
  actions.foldl record { ex }

/--
Begins `prepared`, completes the write of the whole request (one write, for requests no larger than
the write slice), and asks for the whole body.
-/
def written (prepared : PreparedRequest) : Run :=
  let r := begin prepared
  let r := r.apply 0 (.written prepared.bytes.size)
  r.apply 0 (.wantBody (prepared.config.maxBody + 1))

/-- Feeds bytes as one read. -/
def feed (r : Run) (bytes : ByteArray) : Run :=
  r.apply r.ex.now (.received bytes)

/-- Reports end of input. -/
def endOfInput (r : Run) : Run :=
  r.apply r.ex.now .endOfInput

/-- The cause of the failure, if the exchange failed. -/
def failedCause? (r : Run) : Option Cause :=
  match r.ended with
  | some (.fail f) => some f.cause
  | _ => none

end Run

/-- Prepares a request, panicking if the machine refuses it (tests only use valid heads). -/
def prepare! (config : ExchangeConfig) (head : Request.Head) (body : ByteArray) : PreparedRequest :=
  match Exchange.prepare config head body with
  | .ok p => p
  | .error cause => panic! s!"the request was refused: {repr cause}"
