#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Replay controls for the ported fuzzing harness: plants each mutant below in LeanHttp/Exchange.lean
(a scratch edit, restored afterwards), rebuilds the replay tool on the build host and replays the
seeds and the old campaigns' inputs through it, then writes <name>/classes.txt (count and class of
each outcome) and <name>/mutant.diff next to this file.  With no mutant, the unmodified tree
(baseline).

Run from the worktree's root: logs/2026-10-28/fuzz2/controls/mutants.py [name...]
"""

import argparse
import os
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
TARGET = ROOT / "LeanHttp/Exchange.lean"

# name -> (what it breaks, old text, new text)
MUTANTS = {
    "baseline": ("nothing", "", ""),
    "te-undone": ("the transfer-coding refusal is undone",
                  "    if onlyChunked head then none", "    if true then none"),
    "cl-undone": ("the machine's body limit is 2^62 again",
                  "    maxBodySize := max lifted (10 ^ min config.h1.maxHeaderValueLength config.h1.maxHeaderBytes)",
                  "    maxBodySize := lifted"),
    "read-while-sending": ("a read is asked for before the request head is written",
                           "    | .awaitingHead | .draining => true",
                           "    | .sending | .awaitingHead | .draining => true"),
    "deadline-late": ("a deadline is acted on only after it, not at it",
                      "    let passed := candidates.filter fun (t, _, _) => t ≤ now",
                      "    let passed := candidates.filter fun (t, _, _) => t < now"),
    "reuse-leftover": ("reuse ignores bytes left over after the response",
                       " && !ex.machine.hasBufferedInput", ""),
    "fail-no-status": ("a failure carries no status",
                       "      cause, delivery := ex.delivery, written := ex.written, status := ex.head.map (·.status),",
                       "      cause, delivery := ex.delivery, written := ex.written, status := none,"),
}

REPLAY = (
    "rm -rf out/seeds && /py/bin/python3 -I fuzz/seeds.py out/seeds > /dev/null && "
    "lake build Fuzz fuzz-replay 2>&1 | tail -n 1 && "
    "{ ls out/seeds/* ; ls out/old-inputs | sed 's|^|out/old-inputs/|'; } "
    "| xargs -n 500 .lake/build/bin/fuzz-replay --class | sort | uniq -c | sort -rn"
)


def run(name: str) -> None:
    what, old, new = MUTANTS[name]
    original = TARGET.read_text()
    out = HERE / name
    out.mkdir(exist_ok=True)
    try:
        if old:
            assert original.count(old) == 1, f"{name}: the text to replace is not unique"
            TARGET.write_text(original.replace(old, new))
        diff = subprocess.run(["git", "-C", str(ROOT), "diff", "--", str(TARGET)],
                              capture_output=True, text=True, check=True).stdout
        (out / "mutant.diff").write_text(f"# {what}\n{diff}")
        env = dict(os.environ, LEAN_HTTP_REMOTE_DIR="lean-http-fuzz2")
        result = subprocess.run([str(ROOT / "scripts/remote.sh"), "bash", "-c", REPLAY],
                                capture_output=True, text=True, env=env)
        (out / "classes.txt").write_text(
            f"$ scripts/remote.sh bash -c {REPLAY!r}\n{result.stdout}{result.stderr}"
            f"exit status {result.returncode}\n")
    finally:
        TARGET.write_text(original)
    print(f"{name}: {what}")
    print(result.stdout)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("names", nargs="*", help=f"mutants to run (default all): {', '.join(MUTANTS)}")
    args = parser.parse_args()
    unknown = [n for n in args.names if n not in MUTANTS]
    if unknown:
        parser.error(f"unknown mutants: {unknown}")
    for name in args.names or list(MUTANTS):
        run(name)


if __name__ == "__main__":
    main()
