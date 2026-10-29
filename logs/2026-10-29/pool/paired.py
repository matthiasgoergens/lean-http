#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# ///
"""Paired differences per block from bench-idlecheck.sh output: for each cell, the median over
blocks of (cell - off) in the later calls' median time, with a distribution-free 95% interval for
that median (order statistics of the binomial), and the per-cell medians themselves.

Usage: paired.py <bench output>
"""
import math, sys
from collections import defaultdict


def median(xs):
    s = sorted(xs)
    n = len(s)
    return s[n // 2] if n % 2 else (s[n // 2 - 1] + s[n // 2]) / 2


def interval(xs, conf=0.95):
    """Ranks (lo, hi) of a distribution-free interval for the median."""
    s = sorted(xs)
    n = len(s)
    cdf = 0.0
    k = 0
    # largest k with P(Bin(n, 1/2) < k) <= (1 - conf) / 2
    for i in range(n + 1):
        p = math.comb(n, i) / 2 ** n
        if cdf + p > (1 - conf) / 2:
            k = i
            break
        cdf += p
    return s[max(k - 1, 0)], s[min(n - k, n - 1)]


def main():
    rows = defaultdict(dict)
    for line in open(sys.argv[1]):
        parts = line.split()
        if len(parts) == 4 and parts[0].isdigit():
            rows[int(parts[0])][parts[1]] = float(parts[2])
    cells = sorted({c for r in rows.values() for c in r if c != "off"}, key=lambda c: int(c))
    offs = [r["off"] for r in rows.values()]
    print(f"blocks: {len(rows)}")
    print(f"off: median of later-call medians {median(offs):.3f} ms; per block {sorted(offs)}")
    for c in cells:
        vals = [r[c] for r in rows.values()]
        d = [r[c] - r["off"] for r in rows.values()]
        lo, hi = interval(d)
        print(f"window {c} ms: median {median(vals):.3f} ms; paired difference from off: median "
              f"{median(d):+.3f} ms, 95% interval [{lo:+.3f}, {hi:+.3f}]; per block {sorted(round(x, 3) for x in d)}")


main()
