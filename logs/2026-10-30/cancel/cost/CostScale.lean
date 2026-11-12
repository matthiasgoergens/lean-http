import LeanHttp

/-!
# The cost of a call's end on a token shared by k calls in flight

`cost-scale <reps> <k>...` keeps k calls' cancellations registered with one token (`Cancel.watch`,
as `Client.run` makes them for a call given that token) and, in each iteration, starts one more
and ends the oldest (`Cancel.finish`, whose `unregisterFn` scans the token's entries), so the token
holds k entries throughout.  For each repetition, in a fresh random order of the k values, it
prints the time per iteration (one start and one end) in nanoseconds.

Copied into each tree by `build.sh` and built there as the executable `cost-scale`; not part of
lean-http.
-/

open LeanHttp

/-- The watch of a call given `token` (the client's own token is watched by its table). -/
def watchOf (token : Std.CancellationToken) : BaseIO Cancel :=
  Cancel.watch #[token] #[token] -- WATCH

/-- Starts a call's cancellation, as the client does. -/
def startCall (token : Std.CancellationToken) : IO Cancel :=
  watchOf token -- START

/-- Ends it, as the client does. -/
def endCall (c : Cancel) : IO Unit :=
  c.finish -- END

def timeEnds (k iters : Nat) : IO Nat := do
  let token ← Std.CancellationToken.new
  let mut live : Std.Queue Cancel := ∅
  for _ in [0:k] do
    live := live.enqueue (← startCall token)
  let mut t0 := 0
  -- The first tenth warms up.
  for i in [0:iters + iters / 10] do
    if i == iters / 10 then t0 ← IO.monoNanosNow
    let c ← startCall token
    let some (old, rest) := live.dequeue? | pure ()
    endCall old
    live := rest.enqueue c
  let t1 ← IO.monoNanosNow
  for c in live.toArray do endCall c
  return (t1 - t0) / iters

def main (args : List String) : IO UInt32 := do
  let reps := args.head!.toNat!
  let ks := (args.drop 1).map String.toNat!
  for rep in [0:reps] do
    -- A fresh order each repetition: k values in random order.
    let mut order := ks.toArray
    for i in [0:order.size] do
      let j ← IO.rand i (order.size - 1)
      order := order.swapIfInBounds i j
    for k in order do
      let iters := max 2000 (2000000 / (k + 10))
      let ns ← timeEnds (max k 1) iters
      IO.println s!"rep={rep} k={k} iters={iters} ns_per_call={ns}"
  return 0
