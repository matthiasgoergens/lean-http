#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Summary of a scale.sh run: per k and binary, the median time of a call's start and end over the
blocks, with the range.  Usage: scalesummary.py <out.txt>"""
import re
import statistics
import sys
from collections import defaultdict


def main() -> None:
    d: dict[tuple[str, int], list[float]] = defaultdict(list)
    for line in open(sys.argv[1]):
        m = re.match(r"block=\d+ variant=(\w+) load=\S+ k=(\d+) iters=\d+ ns_per_call=(\d+)", line)
        if m:
            d[(m[1], int(m[2]))].append(int(m[3]) / 1000)
    vs = sorted({v for v, _ in d})
    print("start and end of one call's cancellation on a token held by k calls in flight, us: "
          "median [min..max] over blocks")
    for k in sorted({k for _, k in d}):
        print(f"k={k:5d}  " + "  ".join(
            f"{v}: {statistics.median(d[(v, k)]):7.2f} [{min(d[(v, k)]):.1f}..{max(d[(v, k)]):.1f}]" for v in vs))


if __name__ == "__main__":
    main()
