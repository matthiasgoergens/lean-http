#!/usr/bin/env bash
# Runs on the build host itself, under batchrun, from ~/lean-http-cost: who creates the async
# continuations (lean_task_bind_core, lean_task_map_core) of a reused GET.  For each cell, on a copy
# without debug information (as probe.sh), uprobes on both, and perf record with DWARF call graphs
# over <calls> calls; perf report then lists, per probe, the callers in the Lean code (caller
# chains folded), in out/bench/binds-<cell>.txt.  Server on CPU <server cpu>, client on <client cpu>.
# Usage: binds.sh <calls> <server cpu> <client cpu> <cell>...
set -u
calls=$1 scpu=$2 ccpu=$3; shift 3
PY=$HOME/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu/bin/python3
port=${PORT:-18371}
log=out/bench/binds-server-$port.log
cleanup() {
  kill $server 2>/dev/null; wait $server 2>/dev/null
  for c in "$@"; do sudo --non-interactive perf probe --quiet --del "binds_$c:*" 2>/dev/null; done
}
taskset --cpu-list "$scpu" "$PY" -I tests/net/evil.py --port "$port" > "$log" 2>&1 &
server=$!
trap 'cleanup "$@"' EXIT
for _ in $(seq 100); do grep --quiet listening "$log" && break; sleep 0.05; done
for c in "$@"; do
  sha256sum "out/bench/net-client-$c"
  bin=out/bench/probe-net-client-$c
  objcopy --strip-debug "out/bench/net-client-$c" "$bin" || exit 1
  for f in lean_task_bind_core lean_task_map_core; do
    sudo --non-interactive perf probe --quiet -x "$bin" --add "binds_$c:${f}_$c=$f" || exit 1
  done
  sudo --non-interactive perf record --quiet --call-graph=dwarf,16384 \
      --event="binds_$c:lean_task_bind_core_$c" --event="binds_$c:lean_task_map_core_$c" \
      --output="out/bench/binds-$c.data" -- \
      sudo --non-interactive --user="$(id -un)" taskset --cpu-list "$ccpu" "$bin" call GET \
      "http://127.0.0.1:$port/ok" repeat="$calls" trace=0 > /dev/null || exit 1
  sudo --non-interactive perf report --input="out/bench/binds-$c.data" --stdio --no-children \
      --call-graph=caller,0.5,callee --sort=sym 2>/dev/null > "out/bench/binds-$c.txt"
  echo "$c: $(grep --count . "out/bench/binds-$c.txt") lines"
done
