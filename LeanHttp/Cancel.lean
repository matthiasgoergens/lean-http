module

public import Std.Async.Select
import all Std.Async.Select
public import Std.Async.Timer
public import Std.Sync.CancellationToken
public import LeanHttp.Wait

public section

/-!
# Cancelling a call

A call is cancelled through `Std.CancellationToken`s: the one the caller gave it, if any, and the
client's own, which `Client.shutdownNow` cancels.  `Cancel` is the call's view of them.

- `reason?` says whether the call has been cancelled, by asking the tokens themselves, so that a
  check made after a token was cancelled sees it at once, whatever has been scheduled since: the
  shell checks it before each step it takes (before a request goes out, before connecting, before
  an exchange begins, before each read of the body), and after every wait.
- A wait of the call ends at the cancellation (`race`): the wait for a connection at the active cap,
  the name lookup, the connect attempts, the TLS handshake and the sleep before a retry; an exchange
  hears of it through its mailbox (`onCancel`).  What ends the wait decides only which way it ends;
  what happens next is the cores' decision, as for a deadline.

Something must notice a token's cancellation to wake the waits (`fire`).  The call registers a
waiter with the caller's token's selector, which the token resolves inside its `cancel`, and at its
end finishes the waiter and unregisters it, so a token shared by many calls (a program's one
shutdown token, say) holds nothing of the calls that have ended.  The client's own token is shared
by all its calls, so the client keeps a table of its calls in flight instead, and
`Client.shutdownNow` fires each; a call given no token registers with no token.

Firing rings the bell of the wait in progress and runs the hooks the call's exchanges registered.
Each wait arms a bell of its own and checks `reason?` after arming it, so no cancellation is missed,
and each replaces the last, so a call that waits many times (at the active cap, woken by every
connection the client gives back) gathers nothing per wait; a hook registered after the
cancellation runs at once.  Nothing is chained on a promise that outlives the call: the end of the
call drops the last bell and the hooks.
-/

namespace LeanHttp

set_option linter.all true

open Std.Async

/--
The cancellation of one call.
-/
structure Cancel where
  /--
  The tokens that cancel the call.
  -/
  tokens : Array Std.CancellationToken

  /--
  `none` while the call goes on (a token's cancellation, whose reason the token keeps, leaves it so),
  `some (some reason)` once `cancel` has fired it, `some none` once it has ended; only the first
  change counts.
  -/
  state : IO.Ref (Option (Option Std.CancellationReason))

  /--
  The registration with each watched token: the waiter the token resolves when it is cancelled.
  -/
  waiters : Array (Std.CancellationToken × Waiter Unit)

  /--
  The bell of the wait in progress (or of the last one), if a wait has armed one: rung when the call
  is fired.
  -/
  bell : IO.Ref (Option (IO.Promise Unit))

  /--
  What the call's exchanges asked to run when the call is fired (`onCancel`).
  -/
  hooks : IO.Ref (Array (BaseIO Unit))

namespace Cancel

/--
Wakes what waits for the call's cancellation: rings the current bell and runs the hooks, and with a
`reason`, records it first.  The tokens must say so already, or be about to (`reason?` is asked
after waking): a token in `tokens` is cancelled first.  Nothing happens once the call has ended.

A token's waiter is resolved inside the token's `cancel`, which holds the token's mutex and records
the reason only afterwards, so what runs from there must not ask the token anything: neither this
nor what it runs does.  What it wakes asks the tokens later, from tasks of their own.
-/
def fire (state : IO.Ref (Option (Option Std.CancellationReason)))
    (bell : IO.Ref (Option (IO.Promise Unit))) (hooks : IO.Ref (Array (BaseIO Unit)))
    (reason : Option Std.CancellationReason) : BaseIO Unit := do
  let go ← state.modifyGet fun
    | none => (true, reason.map some)
    | other@(some (some _)) => (true, other)
    | other => (false, other)
  if go then
    if let some b ← bell.get then b.resolve ()
    for hook in ← hooks.get do hook

/--
Starts the cancellation of a call that `tokens` cancel: `reason?` asks every one of them, in order,
and the call registers with those in `watched`, whose cancellation fires it.  A token in `tokens`
but not in `watched` must be watched by other means, which fire the call (`cancel`): the client does
so for its own token, which every call shares, by keeping a table of its calls in flight.  Without a
token to watch, this makes no promise and registers nothing.
-/
def watch (tokens watched : Array Std.CancellationToken) : BaseIO Cancel := do
  let state ← IO.mkRef none
  let bell ← IO.mkRef none
  let hooks ← IO.mkRef #[]
  let waiters ← watched.mapM fun token => do
    -- A waiter of the token's selector, as `Selectable.one` would make it (`Waiter.mk` is private
    -- to `Std.Async.Select`, the same in v4.34.1 and v4.35.0).  `Selectable.one` itself hands a win,
    -- and the end of the call, on through tasks of the thread pool, which made every call that was
    -- given a token measurably slower; registering the waiter directly needs no task at all.
    let promise : IO.Promise (Except IO.Error Unit) ← IO.Promise.new
    let waiter : Waiter Unit := Waiter.mk (← IO.mkRef false) promise
    BaseIO.chainTask (sync := true) promise.result? fun
      | some (.ok ()) => fire state bell hooks none
      | _ => pure ()
    discard <| start (token.selector.registerFn waiter)
    return (token, waiter)
  return { tokens, state, waiters, bell, hooks }

/--
Cancels the call for `reason`, from outside the watch: wakes its waits as a watched token's
cancellation would.  The caller must also make `reason?` hold, by cancelling a token in `tokens`
first.
-/
def cancel (c : Cancel) (reason : Std.CancellationReason) : BaseIO Unit :=
  fire c.state c.bell c.hooks (some reason)

/--
Ends the watch, once the call has ended: later cancellations of the tokens do nothing to it, and the
last bell and the hooks, with whatever they hold, are dropped.
-/
def finish (c : Cancel) : BaseIO Unit := do
  c.state.modify fun
    | none => some none
    | other => other
  -- Finish each waiter, so that its token drops it (its selector's `unregisterFn` removes the
  -- finished ones), and release what was chained on it.
  for (token, waiter) in c.waiters do
    waiter.race (pure ()) fun promise => promise.resolve (.error (IO.userError "the call ended"))
    discard <| start token.selector.unregisterFn
  -- The last wait's bell is rung only by a cancellation: dropping it drops what was chained on it.
  c.bell.set none
  c.hooks.set #[]

/--
The reason, if the call has been cancelled: asked of the tokens themselves, in order, so that it
holds as soon as a token is cancelled (or the reason `cancel` gave).  Once the call has ended,
`none`, unless `cancel` fired it before.
-/
def reason? (c : Cancel) : BaseIO (Option Std.CancellationReason) := do
  if let some known ← c.state.get then return known
  for token in c.tokens do
    if let some reason ← token.getCancellationReason then return some reason
  return none

/--
Runs `f` when the call is fired, in the thread that fires it (the one cancelling the token, inside
the token's `cancel`, or the one shutting the client down), or at once if the call has been
cancelled already; never, if the call ends first.  It may run more than once.  It must not ask the
tokens anything (`fire`); what it wakes asks `reason?`.
-/
def onCancel (c : Cancel) (f : BaseIO Unit) : BaseIO Unit := do
  c.hooks.modify (·.push f)
  -- A firing that read the hooks before this one was added: the tokens say so already.
  if (← c.reason?).isSome then f

/--
How a wait that the call's cancellation races ended.
-/
inductive Waited (β : Type) where
  /--
  One of the tasks finished first, with this result.
  -/
  | done (result : β)

  /--
  The time ran out first.
  -/
  | timedOut

  /--
  The call was cancelled first, for `reason`.
  -/
  | cancelled (reason : Std.CancellationReason)

instance {β : Type} : Nonempty (Waited β) := ⟨.timedOut⟩

/--
Waits until one of `tasks` finishes, `IO.monoMsNow` reaches `target` or the call is cancelled,
whichever comes first, as `race` does.
-/
partial def raceUntil {β : Type} (c : Cancel) (tasks : Array (Task β)) (target : Nat)
    (startTimer : StartTimer) : Async (Waited β) := do
  -- A fresh bell first, then the check: a cancellation the check misses rings the new bell.  The
  -- last wait's bell, replaced, is dropped, and what was chained on it with it.
  let bell ← IO.Promise.new
  c.bell.set (some bell)
  if let some reason ← c.reason? then return .cancelled reason
  let (timer, stop) ← startTimer (target - (← IO.monoMsNow))
  let winner : IO.Promise (Waited β) ← IO.Promise.new
  for task in tasks do
    BaseIO.chainTask (sync := true) task fun r => winner.resolve (.done r)
  -- What is chained on the bell may run inside a token's `cancel` (`fire`): it asks nothing, and
  -- holds nothing of `c`, whose `bell` holds the bell.  The reason is asked for below.
  BaseIO.chainTask (sync := true) bell.result? fun
    | some () => winner.resolve (.cancelled .cancel)
    | none => pure ()
  -- A stopped timer drops its promise, which ends `timer` with an error: not a timeout.
  BaseIO.chainTask (sync := true) timer fun
    | .ok () => winner.resolve .timedOut
    | .error _ => pure ()
  -- `winner` is resolved by the timer at the latest, so `result!` cannot be left waiting.
  let result ← await winner.result!
  stop
  -- Something else may have ended the wait after a token was cancelled and before the watch rang
  -- the bell: the cancellation still wins.
  match ← c.reason?, result with
  | some reason, _ => return .cancelled reason
  -- The timer fired before the time had passed (`libuvTimer`): wait for the rest, with a new bell.
  | none, .timedOut =>
    if (← IO.monoMsNow) < target then c.raceUntil tasks target startTimer else return .timedOut
  | none, _ => return result

/--
Waits until one of `tasks` finishes, `ms` milliseconds pass by `IO.monoMsNow` or the call is
cancelled, whichever comes first, like `awaitFirst`, and like it never times out before the time has
passed.  For the call's own task, one wait at a time: each wait replaces the bell of the one before,
so a second wait at the same time would not hear of the cancellation.  The timer is stopped when it
loses; tasks that lose keep running, and it is up to the caller to cancel them.  A call cancelled
already, or cancelled when the wait ends, returns `cancelled`.
-/
def race {β : Type} (c : Cancel) (tasks : Array (Task β)) (ms : Nat)
    (startTimer : StartTimer := libuvTimer) : Async (Waited β) := do
  c.raceUntil tasks ((← IO.monoMsNow) + ms) startTimer

/--
Sleeps until `IO.monoMsNow` reaches `target`, or until the call is cancelled; returns the reason if
it was.
-/
def sleepUntil (c : Cancel) (target : Nat) : Async (Option Std.CancellationReason) := do
  let now ← IO.monoMsNow
  if now < target then
    match ← c.race (#[] : Array (Task Unit)) (target - now) with
    | .cancelled reason => return some reason
    | _ => c.reason?
  else
    c.reason?

end Cancel

end LeanHttp
