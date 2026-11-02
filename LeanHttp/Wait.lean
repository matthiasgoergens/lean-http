module

public import Std.Async.Timer

public section

/-!
# Waiting with a time limit

`Std.Async.race` leaves the loser running.  The client needs to wait for an operation or a timer,
whichever comes first, and then tidy up: stop the timer when the operation won, and let the caller
cancel the operation when the timer won.  Nothing here blocks a thread: every wait is a continuation
on a task, so an abandoned wait never keeps a worker busy or the process alive.

Operations are started with `start`, not `async`.  `async` hands the start of the computation to the
thread pool, so the operation (a timer, a receive) may be registered only after the caller has moved
on, and a cancellation issued in between finds nothing to cancel.
-/

namespace LeanHttp

set_option linter.all true

open Std.Async

/--
Starts `x` in the calling thread: runs it up to its first wait, which registers the operation it
performs, and returns a task for the rest.
-/
def start {α : Type} (x : Async α) : BaseIO (AsyncTask α) :=
  EAsync.toBaseIO x

/--
Starts a one-shot timer of `ms` milliseconds: returns a task that ends when it fires, and an action
that stops it, after which the task ends with an error rather than as a timeout.  `libuvTimer` is
the one the client uses; the tests give `awaitFirst` and `Cancel.race` one that fires early.
-/
abbrev StartTimer := Nat → Async (AsyncTask Unit × IO Unit)

/--
A timer of libuv's event loop (`Std.Async.Sleep`).  It measures its time from the loop's clock,
which the loop reads when it wakes, not when the timer is started: a thread that starts a timer
while the loop is between iterations (waiting for its lock, or not scheduled) starts it from a time
in the past, and it fires that much early by `IO.monoMsNow` (`NOTES.md`, "Timers fire early").
-/
def libuvTimer : StartTimer := fun ms => do
  let sleep ← Sleep.mk (.ofNat ms)
  let timer ← start sleep.wait
  return (timer, sleep.stop)

/--
Waits until one of `tasks` finishes or `IO.monoMsNow` reaches `target`, whichever comes first, as
`awaitFirst` does.
-/
partial def awaitFirstUntil {β : Type} (tasks : Array (Task β)) (target : Nat)
    (startTimer : StartTimer) : Async (Option β) := do
  let (timer, stop) ← startTimer (target - (← IO.monoMsNow))
  let winner : IO.Promise (Option β) ← IO.Promise.new
  for task in tasks do
    BaseIO.chainTask (sync := true) task fun r => winner.resolve (some r)
  -- A stopped timer drops its promise, which ends `timer` with an error: not a timeout.
  BaseIO.chainTask (sync := true) timer fun
    | .ok () => winner.resolve none
    | .error _ => pure ()
  -- `winner` is resolved by the timer at the latest, so `result!` cannot be left waiting.
  let result ← await winner.result!
  stop
  match result with
  -- The timer fired before the time had passed: wait for the rest.  The tasks are chained on again;
  -- a continuation left from the round before resolves a promise that nothing awaits any more.
  | none => if (← IO.monoMsNow) < target then awaitFirstUntil tasks target startTimer else return none
  | some r => return some r

/--
Waits until one of `tasks` finishes or `ms` milliseconds pass by `IO.monoMsNow`, whichever comes
first.  Returns the first result, or `none` on timeout, never before the time has passed: a timer
that fires early (`libuvTimer`) is started again for the rest.  The timer is stopped when a task
wins; tasks that lose keep running, and it is up to the caller to cancel them.
-/
def awaitFirst {β : Type} (tasks : Array (Task β)) (ms : Nat) (startTimer : StartTimer := libuvTimer) :
    Async (Option β) := do
  awaitFirstUntil tasks ((← IO.monoMsNow) + ms) startTimer

/--
Waits for `task` for at most `ms` milliseconds.  Returns its result, or `none` on timeout; on
timeout the task keeps running.
-/
def awaitWithin {α : Type} (task : AsyncTask α) (ms : Nat) : Async (Option (Except IO.Error α)) :=
  awaitFirst #[task] ms

/--
Milliseconds left until `deadline` (a value of `IO.monoMsNow`), or 0 if it has passed.
-/
def remainingMs (deadline : Nat) : BaseIO Nat := do
  return deadline - (← IO.monoMsNow)

end LeanHttp
