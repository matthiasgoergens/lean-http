# Reviews of the exchange core

Two independent reviews of the core and shell at a75c6da (`core.diff` is `git diff ee18238..a75c6da -- LeanHttp/`), run in parallel on 2026-10-28, both asked to refute the guarantees in the module docstring of `LeanHttp/Exchange.lean`:

- `gemini-review.txt`: Gemini 4 Argon (medium) through `agy-readonly`, given `core.diff` and the tree, read-only.
- `claude-review.txt`: a fresh-context Claude (Opus) subagent, given the tree only, read-only; its report as returned.

What came of them:

- Both found that while draining an abandoned body the read gap stayed in `nextDeadline` but was never acted on.  Fixed in b0eb3b6; the checker's new "a live exchange has a deadline ahead" catches it on the unfixed core (`drain-read-gap-before-fix.txt`).
- Claude: a write failure before the response head discarded an early response that might be waiting; the docstring overclaimed about bytes before the request head; a head after a failure in the same batch was not guarded; `Error` dropped the bytes written; and the checker had a property that could not fail.  Fixed in b0eb3b6, 942b77a and ad6914d.
- Gemini: with no body credit left, the end of a chunked body and the end of input mid-body went unnoticed until the caller asked again; and a stalled write that failed late restarted the read gap.  Fixed in 49cac66; the three new traces fail on the unfixed core (`gemini-traces-before-fix.txt`).
- Not acted on: Claude's remaining checker blind spots (no liveness property, so a core that failed every valid response would pass the random runs and the explorer and be caught only by the traces; the read and write gaps' timing is not checked), and the edge case of `gapMs = 0`, where a timer armed by `schedule` is already due and is acted on at the next event or tick.
