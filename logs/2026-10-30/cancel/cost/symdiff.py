#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Instructions per call by symbol from symbols.sh's reports, and the largest differences between
cells.  Usage: symdiff.py <period> <calls> <dir> <a>-<b> ..."""
import math
import re
import sys


def load(path: str) -> dict[str, int]:
    d: dict[str, int] = {}
    for line in open(path):
        m = re.match(r"\s*(\d+)\s+\[\.\]\s+(.*)", line)
        if m:
            name = re.split(r"\s{2,}", m[2].strip())[0]
            d[name] = d.get(name, 0) + int(m[1])
    return d


def main() -> None:
    period, calls, folder = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    per = lambda n: n * period / calls
    cache: dict[str, dict[str, int]] = {}
    for pair in sys.argv[4:]:
        a_name, b_name = pair.split("-")
        a = cache.setdefault(a_name, load(f"{folder}/symbols-{a_name}.txt"))
        b = cache.setdefault(b_name, load(f"{folder}/symbols-{b_name}.txt"))
        total = per(sum(a.values()) - sum(b.values()))
        print(f"{a_name} - {b_name}: {total:+.0f} user instructions per call ({per(sum(a.values())):.0f} - "
              f"{per(sum(b.values())):.0f}); largest differences (+- 2 sd of the sampling):")
        keys = sorted(set(a) | set(b), key=lambda k: -abs(a.get(k, 0) - b.get(k, 0)))
        for k in keys[:22]:
            x, y = a.get(k, 0), b.get(k, 0)
            print(f"  {per(x - y):+7.0f} +-{2 * per(math.sqrt(x + y)):5.0f}  {k[:100]}")
        print()


if __name__ == "__main__":
    main()
