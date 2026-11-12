#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""The primary analysis of PLAN.txt: per-block ratios (cancel / main) of the p50 lines in out.txt,
their median and a 95% bootstrap interval.  Usage: analyse.py out.txt"""
import random, re, statistics, sys
from collections import defaultdict

runs = defaultdict(dict)
for line in open(sys.argv[1]):
    m = re.match(r"block=(\d+) variant=(\w+) p50_ms=([\d.]+) load=([\d.]+)", line)
    if m:
        runs[int(m[1])][m[2]] = float(m[3])
for v in sorted({v for r in runs.values() for v in r} - {"main"}):
    ratios = [r[v] / r["main"] for r in runs.values() if v in r and "main" in r]
    rng = random.Random(1)
    boot = sorted(statistics.median(rng.choices(ratios, k=len(ratios))) for _ in range(10000))
    print(f"{v}/main: blocks={len(ratios)} median ratio={statistics.median(ratios):.3f} "
          f"95% interval={boot[250]:.3f}..{boot[9749]:.3f} "
          f"main p50 median={statistics.median(r['main'] for r in runs.values()):.3f} ms "
          f"{v} p50 median={statistics.median(r[v] for r in runs.values() if v in r):.3f} ms "
          f"{v} slower in {sum(x > 1 for x in ratios)} of {len(ratios)} blocks")
