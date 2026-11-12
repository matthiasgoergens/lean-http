#!/usr/bin/env bash
# Runs on the build host itself, not in the container (perf needs the host's kernel): under batchrun,
# from ~/lean-http-cost, counts what each binary does for <calls> reused GETs to evil.py's /ok, in
# <rounds> rounds that each run every cell once in random order (the cells as in blocks.sh, without
# extra options): perf stat of user and kernel instructions, task-clock and context switches of the
# whole client process.  Server on CPU <server cpu>, client on <client cpu>.
# Usage: count.sh <rounds> <calls> <server cpu> <client cpu> <cell>...
set -u
rounds=$1 calls=$2 scpu=$3 ccpu=$4; shift 4
PY=$HOME/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu/bin/python3
port=${PORT:-18321}
log=out/bench/count-server-$port.log
taskset --cpu-list "$scpu" "$PY" -I tests/net/evil.py --port "$port" > "$log" 2>&1 &
server=$!
trap 'kill $server 2>/dev/null; wait $server 2>/dev/null' EXIT
for _ in $(seq 100); do grep --quiet listening "$log" && break; sleep 0.05; done
for c in "$@"; do sha256sum "out/bench/net-client-$c"; done
for r in $(seq 1 "$rounds"); do
  for c in $(printf '%s\n' "$@" | shuf); do
    load=$(cut --delimiter=' ' --fields=1 /proc/loadavg)
    stat=$(sudo --non-interactive perf stat --field-separator=, \
        --event=instructions:u,instructions:k,task-clock,context-switches,cpu-migrations -- \
        sudo --non-interactive --user="$(id -un)" taskset --cpu-list "$ccpu" "out/bench/net-client-$c" call GET \
        "http://127.0.0.1:$port/ok" repeat="$calls" trace=0 2>&1 >/dev/null \
      | awk -F, '$3 != "" {printf "%s=%s ", $3, $1}')
    echo "round=$r variant=$c load=$load $stat"
  done
done
