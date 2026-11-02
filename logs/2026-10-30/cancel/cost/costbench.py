"""Interleaved timing of reused GETs over loopback, run inside the build container (scripts/remote.sh)
from the repository root with uv's CPython: `/py/bin/python3 -I out/bench/costbench.py ...`.

Each cell is <name>=<binary>[:token], the driver out/bench/cost-bench-<binary> (CostBench.lean),
given a token that is never cancelled with :token.  The run is cut into epochs: each epoch starts
one driver process per cell, all on CPU <client cpu> (evil.py's server on <server cpu>), and then
runs <rounds> rounds; each round asks every cell, in random order, for <calls> calls, so the cells
of one round run within a few milliseconds of each other and share the host's load of that moment.
The processes of an epoch end with it, so each epoch is a fresh sample of process placement.
Prints one line per cell and round (the median, mean and minimum of its calls, and the load
average), and one per cell and epoch with the driver's resource use from wait4.

Usage: costbench.py <epochs> <rounds> <calls> <server cpu> <client cpu> <cell>...
"""
import hashlib
import os
import random
import socket
import statistics
import subprocess
import sys
import time


def main() -> None:
    epochs, rounds, calls = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    scpu, ccpu = sys.argv[4], sys.argv[5]
    cells = []
    for spec in sys.argv[6:]:
        name, _, rest = spec.partition("=")
        binary, _, opt = (rest or name).partition(":")
        cells.append((name, binary, opt == "token"))
    port = int(os.environ.get("PORT", "18331"))
    url = f"http://127.0.0.1:{port}/ok"
    log = open(f"out/bench/costbench-server-{port}.log", "w")
    server = subprocess.Popen(["taskset", "--cpu-list", scpu, sys.executable, "-I", "tests/net/evil.py",
                               "--port", str(port)], stdout=log, stderr=subprocess.STDOUT)
    try:
        for _ in range(200):
            try:
                socket.create_connection(("127.0.0.1", port), timeout=1).close()
                break
            except OSError:
                time.sleep(0.05)
        else:
            sys.exit("the server did not start")
        os.sched_setaffinity(0, {int(ccpu)})
        print(f"host={socket.gethostname()} nproc={os.cpu_count()} epochs={epochs} rounds={rounds} "
              f"calls={calls} server_cpu={scpu} client_cpu={ccpu} cells={' '.join(sys.argv[6:])}", flush=True)
        for _, binary, _ in cells:
            path = f"out/bench/cost-bench-{binary}"
            print(f"sha256 {hashlib.sha256(open(path, 'rb').read()).hexdigest()} {path}", flush=True)
        for epoch in range(epochs):
            run_epoch(epoch, rounds, calls, ccpu, url, cells)
    finally:
        server.terminate()
        server.wait()


def run_epoch(epoch: int, rounds: int, calls: int, ccpu: str, url: str,
              cells: list[tuple[str, str, bool]]) -> None:
    procs = {}
    for name, binary, token in random.sample(cells, len(cells)):
        procs[name] = subprocess.Popen(
            ["taskset", "--cpu-list", ccpu, f"out/bench/cost-bench-{binary}", url] + (["token"] if token else []),
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
    for r in range(rounds):
        load = open("/proc/loadavg").read().split()[0]
        for name, _, _ in random.sample(cells, len(cells)):
            p = procs[name]
            p.stdin.write(f"{calls}\n")
            p.stdin.flush()
            fields = p.stdout.readline().split()
            if not fields:
                sys.exit(f"cell {name} ended early")
            oks, times = int(fields[0]), [int(t) / 1000 for t in fields[1:]]
            print(f"epoch={epoch} round={r} variant={name} load={load} ok={oks} "
                  f"p50_us={statistics.median(times):.1f} mean_us={statistics.mean(times):.1f} "
                  f"min_us={min(times):.1f}", flush=True)
    for name, p in procs.items():
        p.stdin.close()
        _, status, ru = os.wait4(p.pid, 0)
        p.returncode = os.waitstatus_to_exitcode(status)
        print(f"epoch={epoch} variant={name} rusage status={p.returncode} utime={ru.ru_utime:.3f} "
              f"stime={ru.ru_stime:.3f} nvcsw={ru.ru_nvcsw} nivcsw={ru.ru_nivcsw} "
              f"calls={rounds * calls + 1}", flush=True)


if __name__ == "__main__":
    main()
