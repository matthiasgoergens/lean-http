#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""The analysis of a scale-e2e.sh run: per k, the per-block ratio <num>/<den> of the median round
time, its median and a 95% bootstrap interval (10000 resamples of the blocks), and each binary's
median round time.  Usage: scaleanalyse.py <out.txt> <num> <den>"""
import random
import re
import statistics
import sys
from collections import defaultdict


def main() -> None:
    path, num, den = sys.argv[1:4]
    d: dict[int, dict[int, dict[str, float]]] = defaultdict(lambda: defaultdict(dict))
    for line in open(path):
        m = re.match(r"block=(\d+) variant=(\w+) k=(\d+) round_ms=([\d.]+) ok=(\d+)", line)
        if m:
            d[int(m[3])][int(m[1])][m[2]] = float(m[4])
    for k in sorted(d):
        # concurrent=1 makes net-client call one after another, with no round times (0).
        blocks = [b for b in d[k].values() if b.get(num, 0) > 0 and b.get(den, 0) > 0]
        if not blocks:
            print(f"k={k}: no round times")
            continue
        ratios = [b[num] / b[den] for b in blocks]
        rng = random.Random(1)
        boot = sorted(statistics.median(rng.choices(ratios, k=len(ratios))) for _ in range(10000))
        print(f"k={k}: {num}/{den} median ratio={statistics.median(ratios):.3f} 95% interval="
              f"{boot[250]:.3f}..{boot[9749]:.3f} blocks={len(ratios)}; median round "
              f"{den}={statistics.median(b[den] for b in blocks):.2f} ms {num}="
              f"{statistics.median(b[num] for b in blocks):.2f} ms")


if __name__ == "__main__":
    main()
