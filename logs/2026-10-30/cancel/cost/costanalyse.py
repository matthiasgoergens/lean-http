#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""The analysis of a costbench.py run (PLAN.txt): for every cell against main, and for each pair
given as num/den, the per-round ratios of the median call time, their median over all rounds, and a
95% interval from a bootstrap that resamples whole epochs (2000 resamples), since the rounds of one
epoch share their processes; then the same by load half, the per-epoch medians' spread, and each
cell's resource use per call (median over epochs).
Usage: costanalyse.py <out.txt> [num/den ...]"""
import random
import re
import statistics
import sys
from collections import defaultdict


def main() -> None:
    path, extra = sys.argv[1], sys.argv[2:]
    # rounds[(epoch, round)][cell] = (p50, load)
    rounds: dict[tuple[int, int], dict[str, tuple[float, float]]] = defaultdict(dict)
    usage: dict[str, list[dict[str, float]]] = defaultdict(list)
    for line in open(path):
        m = re.match(r"epoch=(\d+) round=(\d+) variant=(\S+) load=([\d.]+) ok=(\d+) p50_us=([\d.]+)", line)
        if m:
            rounds[(int(m[1]), int(m[2]))][m[3]] = (float(m[6]), float(m[4]))
            continue
        m = re.match(r"epoch=(\d+) variant=(\S+) rusage (.*)", line)
        if m:
            usage[m[2]].append({k: float(v) for k, v in re.findall(r"(\w+)=([\d.]+)", m[3])})
    cells = sorted({c for r in rounds.values() for c in r})
    complete = {k: r for k, r in rounds.items() if all(c in r for c in cells)}
    epochs = sorted({e for e, _ in complete})
    print(f"rounds={len(complete)} epochs={len(epochs)} cells={' '.join(cells)}")
    loads = {k: statistics.mean(x[1] for x in r.values()) for k, r in complete.items()}
    mid = statistics.median(loads.values())
    # The halves by rank of the load, so that ties cannot leave one empty.
    ranked = sorted(complete, key=lambda k: loads[k])
    lowkeys = set(ranked[: len(ranked) // 2])
    pairs = ([f"{c}/main" for c in cells if c != "main"] if "main" in cells else []) + extra
    rng = random.Random(1)
    resamples = [[rng.choice(epochs) for _ in epochs] for _ in range(2000)]
    for pair in pairs:
        num, den = pair.split("/")
        by_epoch: dict[int, list[float]] = defaultdict(list)
        for (e, _), r in complete.items():
            by_epoch[e].append(r[num][0] / r[den][0])
        allr = [x for e in epochs for x in by_epoch[e]]
        boot = sorted(statistics.median([x for e in s for x in by_epoch[e]]) for s in resamples)
        lo, hi = boot[int(0.025 * len(boot))], boot[int(0.975 * len(boot)) - 1]
        emed = sorted(statistics.median(by_epoch[e]) for e in epochs)
        low = [r[num][0] / r[den][0] for k, r in complete.items() if k in lowkeys]
        high = [r[num][0] / r[den][0] for k, r in complete.items() if k not in lowkeys]
        print(f"{num}/{den}: median ratio={statistics.median(allr):.4f} 95% interval={lo:.4f}..{hi:.4f}"
              f" (epoch bootstrap); {num} slower in {sum(x > 1 for x in allr)} of {len(allr)} rounds;"
              f" per-epoch medians {emed[0]:.3f}..{emed[-1]:.3f};"
              f" lower load half: {statistics.median(low):.4f}, upper: {statistics.median(high):.4f}")
    lv = sorted(loads.values())
    print(f"load average per round: min={lv[0]:.0f} median={mid:.0f} max={lv[-1]:.0f}")
    for c in cells:
        line = f"{c}: median call {statistics.median(r[c][0] for r in complete.values()):.1f} us"
        if usage[c]:
            for k in ("utime", "stime", "nvcsw", "nivcsw"):
                per = [u[k] / u["calls"] for u in usage[c]]
                scale, unit = (1e6, "us") if k.endswith("time") else (1, "")
                line += f" {k}/call={statistics.median(per) * scale:.1f}{unit}"
        print(line)


if __name__ == "__main__":
    main()
