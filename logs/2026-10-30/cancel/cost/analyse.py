#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""The primary analysis of PLAN.txt: per-block ratios of the p50 lines of a blocks.sh output, their
median and a 95% bootstrap interval (10000 resamples of the blocks), for every cell against main
and for each pair given as num/den; then each cell's median resource use per run, and the ratio
against main in the blocks below and above the median load.
Usage: analyse.py <out.txt> [num/den ...]"""
import random
import re
import statistics
import sys
from collections import defaultdict


def interval(ratios: list[float]) -> tuple[float, float, float]:
    rng = random.Random(1)
    boot = sorted(statistics.median(rng.choices(ratios, k=len(ratios))) for _ in range(10000))
    return statistics.median(ratios), boot[250], boot[9749]


def main() -> None:
    path, pairs = sys.argv[1], sys.argv[2:]
    runs: dict[int, dict[str, dict[str, float]]] = defaultdict(dict)
    for line in open(path):
        m = re.match(r"block=(\d+) variant=(\S+) p50_ms=([\d.]+) load=([\d.]+)(.*)", line)
        if not m:
            continue
        rec = {"p50": float(m[3]), "load": float(m[4])}
        for k, v in re.findall(r"(\w+)=([\d.]+)", m[5]):
            rec.setdefault(k, float(v))
        runs[int(m[1])][m[2]] = rec
    cells = sorted({v for r in runs.values() for v in r})
    complete = [r for r in runs.values() if all(c in r for c in cells)]
    print(f"blocks={len(runs)} complete={len(complete)} cells={' '.join(cells)}")
    pairs = [f"{c}/main" for c in cells if c != "main"] + pairs
    loads = sorted(statistics.mean(x["load"] for x in r.values()) for r in complete)
    mid = statistics.median(loads)
    for pair in pairs:
        num, den = pair.split("/")
        ratios = [r[num]["p50"] / r[den]["p50"] for r in complete]
        med, lo, hi = interval(ratios)
        low = [r[num]["p50"] / r[den]["p50"] for r in complete
               if statistics.mean(x["load"] for x in r.values()) <= mid]
        high = [r[num]["p50"] / r[den]["p50"] for r in complete
                if statistics.mean(x["load"] for x in r.values()) > mid]
        print(f"{num}/{den}: blocks={len(ratios)} median ratio={med:.3f} 95% interval={lo:.3f}..{hi:.3f}"
              f" {num} slower in {sum(x > 1 for x in ratios)} of {len(ratios)};"
              f" load<={mid:.0f}: {statistics.median(low):.3f} load>{mid:.0f}: {statistics.median(high):.3f}")
    print(f"load average per block: min={loads[0]:.0f} median={mid:.0f} max={loads[-1]:.0f}")
    for c in cells:
        rs = [r[c] for r in complete]
        line = f"{c}: p50 median={statistics.median(x['p50'] for x in rs):.3f} ms"
        for k in ("utime", "stime", "nvcsw", "nivcsw"):
            if all(k in x for x in rs):
                line += f" {k}={statistics.median(x[k] for x in rs):g}"
        print(line)


if __name__ == "__main__":
    main()
