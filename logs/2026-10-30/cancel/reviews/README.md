# Reviews of cancelling a call, and of the lookups of a call

## First round

Both reviewers read a snapshot of the branch at 5cf7419 (a detached worktree, with the draft of the
`NOTES.md` section "Cancelling a call", whose measurements were placeholders then), the diff against
main 27a0d86, and the same brief (`prompt-1.txt`):

- a fresh Claude (Opus), as a subagent with no context of this session; `claude-1.txt`;
- Gemini (gemini-4-argon-medium) through `agy-readonly`, run from the snapshot; `gemini-1.txt`.

Both reported defects.  What came of their findings (C for the Claude report, G for Gemini's, with
their numbers):

1. **The call's signal lags `token.cancel`** (C1, G1, G2).  `Selectable.combine` hands a win on through
   `IO.bindTask`, so the signal is resolved from a worker a moment after the token is cancelled.
   `Client.shutdown` cancelled and then closed the pool; the close woke a call waiting at the active
   cap, which found the pool closed and no cancellation yet, and failed with `localClose`.  Confirmed
   by the code; fixed in 1b7b83e: `Cancel.reason?` asks the tokens themselves, and the shell checks it
   at the top of every round of `Attempt.acquire`, before the closed check without pooling, and at the
   top of `Attempt.connect`.  New scenarios `shutdown-cap` and `shutdown-backoff`.
   G1's further claims were refuted: a token cancelled before the call starts *is* seen before
   `Cancel.watch` returns, because `Selectable.one` first calls the combined `tryFn`, which runs the
   case's continuation inline for a selector that is ready; calls after a shutdown were therefore not
   affected (`cancel-before`, which checks that no connection is opened, passes in every run).  G1's
   case C (a callback that cancels and returns at once could have its connection pooled) was real in
   the narrow sense that the connection carried a complete response with nothing unread, so pooling
   was safe; with the token-based check the connection is now closed, as documented.
2. **A continuation per wait on the call's signal** (C3, G4).  Confirmed: a call waiting at the active
   cap waits again whenever any connection of the client comes back.  Fixed: each wait arms a bell of
   its own, which the next wait replaces; one continuation per call rings the current bell.  G4's
   second part (a cancelled or timed-out cap wait leaves its continuation on the client's `freed`
   promise until a connection comes back) was so before the change too; recorded under Left open.
3. **A read handed out bytes the stream held after a cancellation** (C5, G3a).  Confirmed; fixed: the
   read reports the cancellation to the core first when the exchange is still going.  New scenario
   `cancel-held`.
4. **Docstrings that claimed more than the code** (C2, C5, G3b): the `withResponse` docstring's "a body
   that had arrived in full is unaffected", `onCancel`'s "in the thread that cancels it", "before `k`
   is entered".  Fixed: until the final head arrives the call fails; from then on reads raise; once the
   exchange has ended, cancelling changes nothing.  The README and `DESIGN.md` were reworded to match.
5. **A lookup could start after the call was cancelled** (C4, G5a).  Confirmed; fixed by the check at the
   top of `Attempt.connect`.
6. **A round of connect attempts that an attempt won as the call was cancelled returned the socket**
   (G5b), and the call then gave the fresh connection to the pool.  Confirmed; the round now checks the
   cancellation after its loop and drops the socket.  Giving back a connection on which nothing was
   written (cancelled between taking it and beginning the exchange) stays the design, since such a
   connection is clean; the documentation now says so instead of "closed, never pooled".
7. **Theorem docstrings** (C7, G7.1).  `step_cancel` now states which end each phase gets (a finish that
   is not reusable while draining, the failure otherwise); `step_cancel_not_reusable`'s docstring says
   it is about one step.
8. **Test gaps** (C8, G7.2-4).  Fixed: the checker's property compares the cancel's reason and rejects a
   failure while draining; `cancel-write` checks the pool; `cancel-redirect`; `cancel-return` makes a
   second call, not cancelled, which opens a fresh connection (the unused `cancelcalls=N` option, G7.4);
   the calls after a shutdown or a close are checked against the planner (G7.3).  Positive controls
   for every new check are in `../controls/`.  Not tested by sockets, judged impractical to time: a
   cancellation exactly between two hops, and one during a drain; the core's traces and the record
   check cover those paths.  `dns-cancel` needs root, as `dns-timeout` does.
9. **The name `shutdown`** (C, design).  Renamed `shutdownNow`: in Java's `ExecutorService` and HTTP
   client `shutdown` is the graceful one.
10. **A producer started inline holds off the cancellation** until its first wait (C6).  So it held off
    the deadline before; recorded under Left open, not changed.
11. **`lookups` "each host once at most"** (C9, G suspicion).  A lookup that raises an exception is a
    connect failure, which may be retried; the docstrings now say so.
12. **The cap wait's timeout re-enters `acquire`** (G6).  So did the wait it replaced (`awaitFirst`'s
    timeout also matched `some _`); now written as an explicit match, same behaviour.
13. **Suspicions noted, not changed**: the cost of unregistering from a token shared by many calls (a
    scan of its entries; Left open); each exchange's mailbox living until the call ends (Left open);
    `cancel-cap` flaky under load (its detail may now be either "waiting for" or "taking" a connection,
    and the check accepts both).
14. **Design**: both reviewers endorsed a cause of its own, the exchange-core event, reporting a
    cancellation before a request to the planner, the graceful `close` with a separate cancelling
    call, and one lookup per call.  C added that a token cancelled with the reason `deadline` gives
    `cancelled .deadline`, not `timeout .deadline`; now documented.

## Second round

Both reviewers read 1b7b83e (the fixes of the first round), with `prompt-2.txt` and the author's
verdicts on the first round (`verdicts-2.txt`); the Claude reviewer was the same agent, resumed.

1. **The last bell of a call was never released** (C, medium).  What was chained on the bell held the
   call's `Cancel`, whose `bell` field held the bell, and only a cancellation resolved it.  Confirmed by
   the reviewer's probes on v4.34.1 (`claude-2-probes/`); fixed in 415afe8: the end of the call drops
   the bell, and the continuation holds the tokens only.  A unit check, with a planted defect, covers it.
2. **A completion, task or timer ending a wait in the window after the cancellation** (G3) was acted on as
   if nothing had been cancelled (a read failure became `peerClosed`, which may be retried).  Fixed in
   5612056: `Live.next` and `Cancel.race` ask the tokens after their wait.
3. **The window between `acquire`'s check and the pool** (G2): fixed, the closed branch asks the tokens.
4. **A lookup started past the deadline or after the cancellation** (G4, C): `Connect.resolve` checks both
   before it starts one.
5. **Held bytes after an ended exchange** (G1): not changed in code; once the whole body has been handed
   to the stream, the connection was given back clean and what the stream holds is in memory.  The docs
   now say that cancelling changes nothing then (at once for a response without a body).
6. **Cancelling at a step rather than a time** (C): adopted; `cancelon` and the `cancel-steps` scenarios.
   `cancelfrom` and `cancel-cap-waiter` make the cap test unable to pass through the holder's dropped
   connection.
7. **Smaller points**: NOTES' statement of `step_cancel` (fixed); a second wait at once on one `Cancel`
   would miss the cancellation (documented; none happens); the token's mutex taken on each read
   (accepted); the 307/308 delivery nit (pre-existing semantics, not changed).  `idleClean` not racing
   the cancellation (G): not changed, its window is `idleCheckMs`, 0 by default.  Host-name case in the
   lookup cache (G): refuted, the URI parser lowercases names.

## Third round

Both read 5612056 (`prompt-3.txt`, `verdicts-3.txt`) and found no defect in the code.  Gemini's one
finding it refuted in the same report.  The Claude reviewer found that the planted "checks ask only the
signal" defect was not caught by the sockets (now run against the unit checks too, which catch it),
that "abandon drains" was not run against `cancel-steps` (now it is), that `cancelon` did nothing with
`trace=0` (fixed), and a line too long.

## After the third round: the cost

A benchmark (`../bench/`) found the version reviewed so far making a reused GET over loopback 27%
slower without a token.  The client now keeps a table of its calls instead of watching its own token per
call, a caller's token is registered directly rather than through `Selectable.one`, and a call makes no
promise for its cancellation; because a token resolves its waiters inside its `cancel`, holding its
mutex, firing a call no longer asks the token anything.

## Fourth round

Both read 3dfd87d and its documentation edits (`prompt-4.txt`, `verdicts-4.txt`), with the toolchain's
sources at hand.  No defect in the code: the Claude reviewer's probe (`claude-4-probes/`) confirmed that
`Waiter.mk` is reachable, that the waiter's continuation runs inside `cancel`, that asking the token from
there deadlocks (so the rule that firing asks nothing is necessary), and that ending a call leaves the
token with no entry.  Both found documentation still describing the `Selectable.one` watch (fixed in
46df10c and 99e7983), and the Claude reviewer: an overclaim that a call without a token makes no promise
(its waits still arm bells; reworded), no check that an ended call leaves its token (added), a dangling
"The cost" reference (the section now exists), and that a call cancelled by its own token and then by a
shutdown could report `shutdown` (the caller's token is now asked first).  Its design remark, that the
code relies on two private details of Std (`Waiter.mk`, and where `cancel` runs its consumers) where
.NET's `CancellationToken.Register` and Go's `context.AfterFunc` give a public, unregistrable callback,
is recorded in `NOTES.md`; a public function of that kind would be worth proposing to Std.
