#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# ///
"""Paired ratios per block from bench-bigbody.sh output: for the cells `wire` (this branch's
Client.request) and `stream` (its withResponse, read in 64 KiB pulls), the median over blocks of
cell / main (the median of five 60 MB calls in each cell), with a distribution-free 95% interval for
that median (order statistics of the binomial), and the per-cell medians.

Usage: paired.py <bench output>
"""
import math, re, sys
from collections import defaultdict


def median(xs):
    s = sorted(xs)
    n = len(s)
    return s[n // 2] if n % 2 else (s[n // 2 - 1] + s[n // 2]) / 2


def interval(xs, conf=0.95):
    """A distribution-free interval for the median: order statistics k and n - k + 1."""
    s = sorted(xs)
    n = len(s)
    cdf = 0.0
    k = 0
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
        m = re.match(r"block=(\d+) cell=(\w+) (.*)", line)
        if not m:
            continue
        rest = m.group(3)
        p50 = re.search(r"p50=([0-9.]+)", rest)
        value = float(p50.group(1)) if p50 else float(rest.split()[0])
        rows[int(m.group(1))][m.group(2)] = value
    blocks = [r for r in rows.values() if {"main", "wire", "stream"} <= r.keys()]
    print(f"blocks: {len(blocks)}")
    for c in ("main", "wire", "stream"):
        print(f"{c}: median of block medians {median([r[c] for r in blocks]):.1f} ms")
    for c in ("wire", "stream"):
        ratios = [r[c] / r["main"] for r in blocks]
        lo, hi = interval(ratios)
        faster = sum(1 for x in ratios if x < 1)
        print(f"{c} / main: median ratio {median(ratios):.3f}, 95% interval [{lo:.3f}, {hi:.3f}]; "
              f"{c} faster in {faster} of {len(ratios)} blocks; per block "
              f"{sorted(round(x, 3) for x in ratios)}")


main()
