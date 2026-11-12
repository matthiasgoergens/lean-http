#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# ///
"""Plants one deliberate bug in LeanHttp/Exchange.lean of a scratch copy of the tree, for the
positive controls of core-tests.  Usage: plant.py <tree> <name>.  Never run on the worktree."""
import sys
from pathlib import Path

PLANTS = {
    # The core counts a write as done when it issues it, so it reads (and can deliver a head)
    # before the request head has been written.
    "head-before-write": (
        "      writeInFlight := some (stop - ex.written), writeBy := some (ex.now + ex.config.gapMs),\n"
        "      sentAny := true }\n",
        "      writeInFlight := some (stop - ex.written), writeBy := some (ex.now + ex.config.gapMs),\n"
        "      sentAny := true,\n"
        "      phase := match ex.phase with\n"
        "        | .sending => if stop ≥ ex.headBytes then .awaitingHead else .sending\n"
        "        | p => p }\n",
    ),
    # A second write is issued while one is in flight.
    "two-writes": (
        "  if !ex.uploadStopped && ex.writeInFlight.isNone && ex.written < ex.request.size then\n",
        "  if !ex.uploadStopped && ex.written < ex.request.size then\n",
    ),
    # The reuse verdict ignores bytes left over after the response.
    "reuse-with-leftovers": (
        " && !ex.inputEnded && !ex.machine.hasBufferedInput\n",
        " && !ex.inputEnded\n",
    ),
    # "Not sent" when no write has completed, although one was issued.
    "not-sent-while-writing": (
        "  else if ex.sentAny then .maybeDelivered\n",
        "  else if ex.written > 0 then .maybeDelivered\n",
    ),
}

tree, name = Path(sys.argv[1]), sys.argv[2]
if (tree / ".git").exists():
    sys.exit("plant.py: refusing to plant in a Git checkout")
old, new = PLANTS[name]
path = tree / "LeanHttp/Exchange.lean"
text = path.read_text()
if text.count(old) != 1:
    sys.exit(f"plant.py: the text to replace for {name} occurs {text.count(old)} times")
path.write_text(text.replace(old, new))
print(f"planted {name}")
