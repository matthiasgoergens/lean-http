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
Waits until one of `tasks` finishes or `ms` milliseconds pass, whichever comes first.  Returns the
first result, or `none` on timeout.  The timer is stopped when a task wins; tasks that lose keep
running, and it is up to the caller to cancel them.
-/
def awaitFirst {β : Type} (tasks : Array (Task β)) (ms : Nat) : Async (Option β) := do
  let sleep ← Sleep.mk (.ofNat ms)
  let timer ← start sleep.wait
  let winner : IO.Promise (Option β) ← IO.Promise.new
  for task in tasks do
    BaseIO.chainTask (sync := true) task fun r => winner.resolve (some r)
  -- A stopped timer drops its promise, which ends `timer` with an error: not a timeout.
  BaseIO.chainTask (sync := true) timer fun
    | .ok () => winner.resolve none
    | .error _ => pure ()
  -- `winner` is resolved by the timer at the latest, so `result!` cannot be left waiting.
  let result ← await winner.result!
  sleep.stop
  return result

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
