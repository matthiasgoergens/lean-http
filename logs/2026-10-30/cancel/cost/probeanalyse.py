#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Counts per call from a probe.sh or count.sh output: for probe.sh, each round's
(count at n2 - count at n1) / (n2 - n1) per event and cell; for count.sh, each run's count divided
by its calls.  Prints the median over rounds and the range, per event, with each cell's difference
from main.  Usage: probeanalyse.py <out.txt> [calls per run, for count.sh output]"""
import re
import statistics
import sys
from collections import defaultdict


def main() -> None:
    path = sys.argv[1]
    per_run_calls = int(sys.argv[2]) if len(sys.argv) > 2 else None
    # runs[(round, cell)][calls] = {event: count}
    runs: dict[tuple[int, str], dict[int, dict[str, float]]] = defaultdict(dict)
    for line in open(path):
        m = re.match(r"round=(\d+) variant=(\S+) (?:calls=(\d+) )?load=[\d.]+ (.*)", line)
        if not m:
            continue
        counts = {k: float(v) for k, v in re.findall(r"(\S+?)=([\d.]+)", m[4])}
        calls = int(m[3]) if m[3] else per_run_calls
        runs[(int(m[1]), m[2])][calls] = counts
    per: dict[str, dict[str, list[float]]] = defaultdict(lambda: defaultdict(list))
    for (_, cell), by_calls in runs.items():
        ns = sorted(by_calls)
        if len(ns) >= 2:
            lo, hi = ns[0], ns[-1]
            for ev in by_calls[hi]:
                if ev in by_calls[lo]:
                    per[cell][ev].append((by_calls[hi][ev] - by_calls[lo][ev]) / (hi - lo))
        else:
            for ev, v in by_calls[ns[0]].items():
                per[cell][ev].append(v / ns[0])
    cells = sorted(per, key=lambda c: (c != "main", c))
    events = sorted({ev for c in cells for ev in per[c]})
    print("per call: median over rounds [min..max]; (difference from main's median)")
    for ev in events:
        print(ev)
        base = statistics.median(per["main"][ev]) if ev in per.get("main", {}) else None
        for c in cells:
            xs = per[c].get(ev)
            if not xs:
                continue
            med = statistics.median(xs)
            diff = f" ({med - base:+.1f})" if base is not None and c != "main" else ""
            print(f"  {c}: {med:.1f} [{min(xs):.1f}..{max(xs):.1f}] n={len(xs)}{diff}")


if __name__ == "__main__":
    main()
