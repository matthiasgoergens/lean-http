#!/usr/bin/env bash
# Runs inside the build container (scripts/remote.sh), from the repository root: randomised blocks
# of reused GETs over loopback.  Each cell is <name>=<binary>[:<extra key=value>...]; a bare <name>
# is the binary out/bench/net-client-<name> with no extra options.  Each block runs every cell once,
# in random order, each making <calls> calls through one client to evil.py's /ok, on CPU <client
# cpu>, with the server on <server cpu>.  One line per run: the cell, the client's "summary later
# calls" (the calls after the first), the load average when it started, and the client's resource
# use from wait4 (user and system CPU seconds, voluntary and involuntary context switches).
# The script is not in the copy remote.sh makes (logs/ is left out), and systemd-run (under
# batchrun) expands ${...} in a command line, so it is copied to out/bench/ and run from there:
#   scp blocks.sh <host>:lean-http-cost/out/bench/ && scripts/remote.sh bash out/bench/blocks.sh <args>
# Usage: blocks.sh <blocks> <calls> <server cpu> <client cpu> <cell>...
set -u
blocks=$1 calls=$2 scpu=$3 ccpu=$4; shift 4
cells=("$@")
PY=${PY:-/py/bin/python3}
port=${PORT:-18311}
log=out/bench/server-$port.log
# Runs a command and prints its output, then one line of its resource use.
rusage='
import os, sys
pid = os.fork()
if pid == 0:
    os.execv(sys.argv[1], sys.argv[1:])
_, status, ru = os.wait4(pid, 0)
print(f"rusage status={os.waitstatus_to_exitcode(status)} utime={ru.ru_utime:.3f} stime={ru.ru_stime:.3f} nvcsw={ru.ru_nvcsw} nivcsw={ru.ru_nivcsw}", flush=True)
'
taskset --cpu-list "$scpu" "$PY" -I tests/net/evil.py --port "$port" > "$log" 2>&1 &
server=$!
trap 'kill $server 2>/dev/null; wait $server 2>/dev/null' EXIT
for _ in $(seq 100); do grep --quiet listening "$log" && break; sleep 0.05; done
grep --quiet listening "$log" || { echo "server did not start" >&2; exit 1; }
echo "host=$(hostname) nproc=$(nproc) calls=$calls server_cpu=$scpu client_cpu=$ccpu cells=${cells[*]}"
for c in "${cells[@]}"; do
  bin=${c#*=}; bin=${bin%%:*}
  sha256sum "out/bench/net-client-$bin"
done
for b in $(seq 1 "$blocks"); do
  for i in $(seq 0 $((${#cells[@]} - 1)) | shuf); do
    c=${cells[$i]}
    name=${c%%=*} spec=${c#*=}
    bin=${spec%%:*}
    extra=()
    if [ "$spec" != "$bin" ]; then IFS=: read -r -a extra <<< "${spec#*:}"; fi
    load=$(cut --delimiter=' ' --fields=1 /proc/loadavg)
    out=$(taskset --cpu-list "$ccpu" "$PY" -I -c "$rusage" "out/bench/net-client-$bin" call GET \
      "http://127.0.0.1:$port/ok" repeat="$calls" trace=0 "${extra[@]}")
    summ=$(sed --quiet 's/^summary later calls //p' <<< "$out")
    ru=$(sed --quiet 's/^rusage //p' <<< "$out")
    p50=$(sed --quiet 's/.* p50=\([0-9.]*\) .*/\1/p' <<< "$summ")
    ok=$(sed --quiet 's/^summary calls .* ok=\([0-9]*\)$/\1/p' <<< "$out")
    echo "block=$b variant=$name p50_ms=$p50 load=$load ok=$ok $ru $summ"
  done
done
