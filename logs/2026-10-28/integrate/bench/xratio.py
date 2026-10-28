#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# ///
"""Paired per-block ratios of the large-body benchmark, with a distribution-free 95% interval for
each median (order statistics of the binomial sign test).

- codec-bench output (bench-*.txt): in each block, the core over the former core (the oracle copy,
  `machine`), both in one binary.
- xbench.sh output (xbench-*.txt): in each block, the branch's core over main's own core, and the
  oracle copy of main's core over main's own core, from the two binaries run in turn.

Usage: ./xratio.py <file>...
"""
import math
import statistics
import sys


def interval(rs: list[float]) -> tuple[float, float]:
    """95% interval for the median: order statistics k and n + 1 - k, k from the normal
    approximation to the binomial."""
    n = len(rs)
    k = max(1, math.floor(n / 2 - 1.96 * math.sqrt(n) / 2))
    return rs[k - 1], rs[n - k]


def report(label: str, rs: list[float]) -> None:
    rs = sorted(rs)
    lo, hi = interval(rs)
    below = sum(r < 1 for r in rs)
    print(f"{label}: median {statistics.median(rs):.3f} (95% interval {lo:.3f} to {hi:.3f}), "
          f"below 1 in {below} of {len(rs)} blocks")


def main(paths: list[str]) -> None:
    for path in paths:
        print(f"== {path}")
        t: dict[tuple[str, int], int] = {}
        for line in open(path):
            if line.startswith("obs "):
                _, cell, block, ns = line.split()
                t[(cell, int(block))] = int(ns)
        blocks = sorted({b for _, b in t})
        cells = {c for c, _ in t}
        for w in ["length", "chunked16k", "chunked1k"]:
            if f"machine-{w}" in cells:
                report(f"{w}: core / former core",
                       [t[(f"core-{w}", b)] / t[(f"machine-{w}", b)] for b in blocks])
            if f"main-core-{w}" in cells:
                report(f"{w}: branch core / main's core",
                       [t[(f"branch-core-{w}", b)] / t[(f"main-core-{w}", b)] for b in blocks])
                report(f"{w}: oracle copy / main's core",
                       [t[(f"branch-machine-{w}", b)] / t[(f"main-core-{w}", b)] for b in blocks])


if __name__ == "__main__":
    main(sys.argv[1:])
