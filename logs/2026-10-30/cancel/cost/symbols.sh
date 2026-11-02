#!/usr/bin/env bash
# Runs on the build host itself, under batchrun, from ~/lean-http-cost: where each binary's user-space
# instructions go.  For each cell, net-client makes <calls> reused GETs to evil.py's /ok under
# perf record sampling user instructions every <period>; perf report then gives the samples per
# symbol, written to out/bench/symbols-<cell>.txt (columns: samples, symbol).  Instructions per call
# in a symbol are samples * period / calls.  Server on CPU <server cpu>, client on <client cpu>.
# Usage: symbols.sh <calls> <period> <server cpu> <client cpu> <cell>...
set -u
calls=$1 period=$2 scpu=$3 ccpu=$4; shift 4
PY=$HOME/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu/bin/python3
port=${PORT:-18361}
log=out/bench/symbols-server-$port.log
taskset --cpu-list "$scpu" "$PY" -I tests/net/evil.py --port "$port" > "$log" 2>&1 &
server=$!
trap 'kill $server 2>/dev/null; wait $server 2>/dev/null' EXIT
for _ in $(seq 100); do grep --quiet listening "$log" && break; sleep 0.05; done
for c in "$@"; do
  sha256sum "out/bench/net-client-$c"
  sudo --non-interactive perf record --quiet --event=instructions:u --count="$period" \
      --output="out/bench/symbols-$c.data" -- \
      sudo --non-interactive --user="$(id -un)" taskset --cpu-list "$ccpu" "out/bench/net-client-$c" call GET \
      "http://127.0.0.1:$port/ok" repeat="$calls" trace=0 > /dev/null || exit 1
  sudo --non-interactive perf report --input="out/bench/symbols-$c.data" --stdio --no-children \
      --sort=symbol --fields=sample,symbol 2>/dev/null | grep -v '^#' | grep -v '^$' > "out/bench/symbols-$c.txt"
  echo "$c: $(awk '{s += $1} END {print s}' "out/bench/symbols-$c.txt") samples"
done
