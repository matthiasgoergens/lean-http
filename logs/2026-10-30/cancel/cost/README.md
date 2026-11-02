# How much of the cost of watching for cancellation can be given back

Runs of 2 November 2026 (times UTC+8), on the shared build host (128 CPUs; load averages 110 to
over 1000 during the runs, mostly 200 to 500), from the worktree of branch `cancel-cost` at
86307b0.  `PLAN.txt` was written before the first run, with an addendum before each later one.
Every build is from `git archive` of a commit through `scripts/remote.sh` (`build.sh`), toolchain
v4.34.1 (`build.txt`: every commit and every binary's SHA-256), the image `localhost/b8perf-lean`;
servers run on uv's CPython 3.14.8.  Every run's output is kept, with the exact command in the
`COMMAND` file next to it; the large ones are compressed (`out.txt.xz`: `xz --decompress --keep`
before running the analysis scripts on them).

## The variants

Commits on local branches, saved as patches in `variants/` (against 86307b0, or main 27a0d86 for
mainpert):

- main 27a0d86; cancel 86307b0, the branch; token, the branch with a token never cancelled.
- mainpert (a3effbc): main with an unused function before the client's code, a control of what code
  placement alone moves.
- ceiling (f20dc26): a call given no token skips watch, track, finish and every check and race;
  `shutdownNow` no longer reaches it, so it is an upper bound only.
- flag (e2a9e81): `shutdownNow` sets an `IO.Ref` that each check reads, in place of the client's
  token, whose mutex every check of every call took.
- finish (af8baa0): `finish` does nothing for a call given no token.  flagfinish (410a088): both.
- cache (9145f02, on flag): the waiter a call registers with its token records, inside the token's
  `cancel`, that the token fired; a check reads the call's state and the flag, and asks the token
  only after it fired, so no lock is taken in the common path.
- sweep (4331720, on cache) and sweep2 (a3dee6b, on the branch): the end of a call sweeps a token's
  entries (Std's `unregisterFn`, a scan of all of them) only once as many calls on the token have
  ended as remain, and when the last ends, counting per token in the client.  sweep counts under a
  lock of its own, sweep2 under the lock of the client's table of calls, which every call takes
  anyway.

## How the timing was done

The last round's design (`blocks.sh` here, as in `../bench/`) did not survive the load: in the
pilots (`pilot/`) the per-block log ratios had a standard deviation of 0.25 to 0.43, three to four
times the last round's, which would have needed about 5000 blocks for +-1%.  The timing moved to
interleaved rounds (`costbench.py`, `CostBench.lean`): one long-lived driver process per cell, all
on CPU 101 with evil.py on CPU 100, each round asking every cell, in random order, for 20 reused
GETs, so the cells of a round share the load of the same few milliseconds; the processes are
replaced every epoch, and the interval comes from a bootstrap over whole epochs
(`costanalyse.py`).  The driver makes the same GET with the same client configuration and timing
as net-client with `trace=0`; it is built into each tree by `build.sh` and is not part of
lean-http.  Counts per call (`probe.sh`, `probeanalyse.py`: uprobes on Lean runtime functions,
scheduler and futex tracepoints and user instructions, each binary run at 200 and 2200 calls and
differenced) and an instruction profile by symbol (`symbols.sh`, `symdiff.py`) were taken on the
host itself with perf.

## Results

**The ceiling** (run1/, 60 epochs of 200 rounds, load 178 to 269; run2/, 200 epochs of 50, load
113 to 679, median 255).  Against cancel, median of per-round ratios: 0.955 (95% interval 0.933
to 0.975) in run 1, 0.977 (0.965 to 0.987) in run 2.  Against main: cancel 1.050 (1.027 to 1.076)
and 1.040 (1.029 to 1.051); ceiling 1.000 (0.983 to 1.018) and 1.012 (1.003 to 1.022).  The
layout control mainpert: 1.001 (0.984 to 1.020) and 1.005 (0.997 to 1.013).  So skipping all of
the cancellation work for a call given no token gives back 2.5 to 4.5% of a call at this load,
most of the gap with main.

**The candidates that keep the semantics** (run2/, against cancel unless said): flag 1.006 (0.995
to 1.019), finish 1.003 (0.993 to 1.012), flagfinish 0.999 (0.989 to 1.009), cache 1.002 (0.992
to 1.012); for a call with a token, against token: flag-token 0.998 (0.988 to 1.007), cache-token
0.991 (0.980 to 1.001).  None gives back anything measurable, and none is kept.  A token never
cancelled costs a call 1.022 (1.014 to 1.035) against none.

**Where the cost is** (probe/, symbols/).  Per call, user instructions: main about 337,000; cancel
30,000 more (cache 27,000, flagfinish 26,000), the ceiling 19,000 more (probe/; symbols/ gives
28,500 and 12,200 by its sampling).  Mutex acquisitions: main 2, cancel 11 (the two of the table,
seven checks of the client's token), flagfinish and cache 4, the ceiling 2: flag removes seven
lock round trips a call, and the timing cannot see them.  `lean_mark_mt` calls: main 84, cancel
98, flagfinish 93, the ceiling 88, so marking objects as shared between threads is part of the
cost, as the prior-art notes guessed (the call's `Cancel` entering the client's table, and the
closures it holds), about 2,600 instructions of the 16,000 between cancel and the ceiling.  Task
continuations (`lean_task_bind_core` and `lean_task_map_core`): 2.4 more a call in cancel, 1.4
more in the ceiling, each a possible hop between threads.  The rest of the difference between
cancel and main is spread over closure calls (`lean_apply_2`), allocation and freeing; nothing
stands out.  What remains in the ceiling (about 12,000 instructions and 1.4 continuations a call)
is code on the exchange path whatever the token: the `Cancel` threaded through the shell, the
exchange's added state, and their closures.  An attempt to attribute the continuations to their
callers (binds/) failed: perf could not unwind from the uprobes, and the reports hold no call
chains.  Context switches per call (about 165 to 180 sched_switch events, on a client whose
threads share one CPU) vary too much between runs to tell the binaries apart.

**The scaling** of a call's end on a token shared by k calls in flight.  The microbenchmark
(scale2/, `CostScale.lean`: start one call's cancellation and end the oldest, the token holding k
throughout, 10 blocks) gives, per start and end, cancel 1.6 µs at k = 1, 10.3 at 128, 81 at 1024,
584 at 4096; sweep2 2.6, 1.7, 2.4 and 2.7 (scale/ has the same for cancel, cache and sweep, with
the driver before it counted as the client does).  So the scan costs about 80 ns per entry, and
counting makes the end of a call constant in k.  End to end (run3b/, rounds of k concurrent GETs
through one client, all given one token, 30 blocks), sweep2 against cancel: k = 16 0.986 (0.710 to
1.403), k = 128 0.948 (0.897 to 1.013), k = 512 0.924 (0.890 to 1.027), neither interval excluding
no change; the microbenchmark predicts only 1% and 2% of a round at 128 and 512.  At k = 2048,
added after seeing those (run3d/, 10 blocks of 10 rounds, load 316 to 1075): 0.792 (0.537 to
1.201), the gap large in the first four blocks, at loads of 440 to 630, and gone in the last four,
at about 320.  At k = 1, a call given its own token: sweep2-token against token 1.001 (0.987 to 1.017) (run3c/, 100
epochs of 50 rounds); sweep, with a lock of its own, cost about 1% (run2/, sweep-token against
cache-token 1.012, 1.001 to 1.023), which is why sweep2 counts under the table's lock.

**What was kept: nothing.**  No candidate met the rule of `PLAN.txt`: none of the changes for a
call without a token, or with one, gave back anything measurable, and sweep2, whose effect on the
cost of a call's end is clear in the microbenchmark, did not show 2% end to end with an interval
excluding no change at any k tried.  Its unit checks pass (`variants/sweep2-unit.txt`, 204 checks,
three of them new, on the counting); the full CI script was not run on it, since it is not kept.

Shuffled-section builds were not made: no decision turned on an effect under 3%.  The candidates
were within 1% of no change, the layout control moved by under 1%, and the ceiling's 2.5 to 4.5%
decided only that the candidates were worth measuring.

## Notes on the runs

- `pilot/` holds the two pilots of `blocks.sh` (for the noise only), its smoke run, a first try of
  perf instruction counts (`count.sh`, superseded by `probe.sh`, which also takes out the
  process's start) and a smoke run of `costbench.py`.
- `blocks.sh`, `costbench.py`, `probe.sh`, `scale.sh` and `scale-e2e.sh` are copied to the
  remote `out/bench/` and run from there: systemd-run, under batchrun, expands `${...}` in a
  command line, which mangled the last round's way of passing a script with `bash -c`.
- In run3d one run of cancel at k = 2048 had calls fail (17,900 of 20,480 succeeded) at a load
  average of over 1000.
- Builds of sweep2 failed for a while with "create keyring: Disk quota exceeded": the kernel's
  limit of 200 keys per user was nearly used up by the containers of other sessions of the same
  user; the builds went through once it dropped.
