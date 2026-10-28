# Reviews of the restated theorems

Both reviewers read a read-only snapshot of the tree at c61733b of the untidied history (branch
integrate-log; the theorems as first written, before the strengthening below), with the same prompt
(prompt.txt):

- a fresh Claude (Opus), as a subagent with no context of this session, on /tmp/integ/review-snap;
  its report is claude.txt;
- Gemini (gemini-4-argon-medium) through ~/.local/bin/agy-readonly, run from the snapshot; gemini.txt.

Both found every statement to agree with its docstring and none vacuous.  What came of their findings
(numbers as in claude.txt):

1. Framing, keep-alive and the Std.Http head not tied to the bytes (Claude; Gemini noted the same of
   keep-alive).  Fixed: observed_finish_codec and observed_finish_complete conclude Codec.HeadOK.
2. "Every head allowed keep-alive" is code, not theorem, for interim heads (both).  Fixed in the
   docstrings and in DESIGN.md/NOTES.md; left open as a codec gap.
3. "The head the core delivered" is the core's head field.  Docstrings now point at step_deliverHead.
4. The end-of-input part of "finish only after a complete response" was only implied.  Added to
   observed_finish_complete (hd.framing = .untilClose → m'.eofSeen = true), proved with the codec's
   NoUCDone.
5. observed_body_prefix cites feed_respSound only.  The docstring now cites finish_respSound too.
6. Obs.fed's docstring omitted "before the run ended".  Fixed, and in the checker's Model.fed.

A second Gemini pass (gemini-2.txt), on the strengthened statements in the worktree, found two more:

7. observed_finish_codec constrained the body in the bytes only when the caller had not abandoned,
   though the docstring claimed it always.  Fixed: the conclusion now says the body in the bytes is a
   body of its framing carrying the payload the codec decoded, unconditionally, and, unless
   abandoned, that the body delivered is that payload.
8. Codec.HeadOK ties the framing and the Std.Http head to the fields exactly, but the keep-alive
   verdict only one way.  The docstrings now say "allows keep-alive only if its own version and
   fields do".
Both changes are in e5966fe; suites/final-ed36708 has the build and axioms after them.
