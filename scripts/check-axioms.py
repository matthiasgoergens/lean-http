#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Checks the axioms of the theorems that `#print axioms` lines name.

Runs `lake env lean` on each script given (scripts/*-axioms.lean) from the repository root and fails
unless it exits with status 0, prints nothing but axiom reports, reports every `#print axioms` line
of the script, and every theorem depends on no axioms beyond propext, Classical.choice and
Quot.sound (so on no sorryAx).

Usage: scripts/check-axioms.py <script.lean>...
"""

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
PRINT_LINE = re.compile(r"^\s*#print\s+axioms\s+\S+", re.MULTILINE)
# One report: `'name' depends on axioms: [a, b,\n c]` or `'name' does not depend on any axioms`.
REPORT = re.compile(
    r"'(?P<name>[^']+)' (?:depends on axioms: \[(?P<axioms>[^\]]*)\]|does not depend on any axioms)\n?"
)


@dataclass(frozen=True)
class Verdict:
    script: Path
    theorems: int
    problems: list[str]


def check(root: Path, script: Path) -> Verdict:
    expected = len(PRINT_LINE.findall(script.read_text()))
    run = subprocess.run(
        ["lake", "env", "lean", str(script)], cwd=root, capture_output=True, text=True
    )
    problems = []
    if run.returncode != 0:
        problems.append(f"lean exited with status {run.returncode}")
    if run.stderr.strip():
        problems.append(f"lean wrote to stderr: {run.stderr.strip()}")
    reports = list(REPORT.finditer(run.stdout))
    leftover = REPORT.sub("", run.stdout).strip()
    if leftover:
        problems.append(f"output that is not an axiom report: {leftover}")
    if expected == 0:
        problems.append("the script has no #print axioms lines")
    if len(reports) != expected:
        problems.append(f"{len(reports)} axiom reports for {expected} #print axioms lines")
    for r in reports:
        axioms = {a.strip() for a in (r["axioms"] or "").split(",") if a.strip()}
        if axioms - ALLOWED:
            problems.append(f"{r['name']} depends on {sorted(axioms - ALLOWED)}")
    return Verdict(script, len(reports), problems)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("scripts", nargs="+", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    failed = False
    for script in args.scripts:
        verdict = check(root, script.resolve())
        if verdict.problems:
            failed = True
            print(f"FAIL {script}:")
            for p in verdict.problems:
                print(f"  {p}")
        else:
            print(f"ok {script}: {verdict.theorems} theorems, none beyond {', '.join(sorted(ALLOWED))}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
