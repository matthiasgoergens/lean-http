#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Checks that every Lean code block of a Markdown file appears in a Lean file of the examples
directory, which CI compiles and runs: as consecutive lines that are the block's, once both are
stripped of their common indentation.  Blocks that start with `require` are lakefile
snippets for a user's package and are skipped: the examples' own lakefile requires this package by
path, and the README's blocks name the Git URL.

Usage: scripts/check-readme.py README.md examples
"""

import argparse
import re
import sys
import textwrap
from pathlib import Path

BLOCK = re.compile(r"^```lean\n(.*?)^```", re.MULTILINE | re.DOTALL)


def contains(text: str, block: str) -> bool:
    """Whether some run of consecutive lines of `text`, dedented, is `block`, dedented."""
    wanted = textwrap.dedent(block).rstrip("\n").splitlines()
    lines = text.splitlines()
    n = len(wanted)
    return any(
        textwrap.dedent("\n".join(lines[i : i + n])).splitlines() == wanted
        for i in range(len(lines) - n + 1)
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("markdown", type=Path)
    parser.add_argument("examples", type=Path)
    args = parser.parse_args()
    sources = {p: p.read_text() for p in sorted(args.examples.rglob("*.lean")) if ".lake" not in p.parts}
    blocks = BLOCK.findall(args.markdown.read_text())
    missing = 0
    checked = 0
    for block in blocks:
        if block.lstrip().startswith("require"):
            continue
        checked += 1
        homes = [p for p, text in sources.items() if contains(text, block)]
        first = block.splitlines()[0] if block.strip() else "(empty)"
        if homes:
            print(f"ok   {first!r} is in {homes[0]}")
        else:
            missing += 1
            print(f"FAIL {first!r} is in no file under {args.examples}:\n{block}")
    if checked == 0:
        print(f"FAIL no Lean blocks to check in {args.markdown}")
        return 1
    print(f"{checked} Lean blocks checked, {missing} not in an example")
    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main())
