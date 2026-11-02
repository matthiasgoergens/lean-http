#!/usr/bin/env bash
# Runs inside the build container (scripts/remote.sh), from the repository root: randomised blocks
# of reused GETs over loopback, main's net-client against this branch's (out/bench/, made by
# build.sh): this branch's without a cancellation token (variant cancel) and with one that is never
# cancelled (variant token, cancelon=none).  Each block runs the three variants once, in random
# order, each making <calls> calls through one client to evil.py's /ok; the statistic is the
# median time of the calls after the first (net-client's "summary later calls").  The server runs
# on CPU <server cpu>, the clients on <client cpu>.  Prints one line per run, with the load average.
# The script is not in the copy remote.sh makes (logs/ is left out), so it is run as
#   scripts/remote.sh bash -c "$(cat logs/2026-10-30/cancel/bench/blocks.sh)" blocks.sh <args>
# Usage: blocks.sh <blocks> <calls> <server cpu> <client cpu>
set -u
blocks=$1 calls=$2 scpu=$3 ccpu=$4
PY=${PY:-/py/bin/python3}
port=18299
log=out/bench/server.log
taskset --cpu-list "$scpu" "$PY" -I tests/net/evil.py --port $port > "$log" 2>&1 &
server=$!
trap 'kill $server 2>/dev/null; wait $server 2>/dev/null' EXIT
for _ in $(seq 100); do grep --quiet listening "$log" && break; sleep 0.05; done
sha256sum out/bench/net-client-main out/bench/net-client-cancel
for b in $(seq 1 "$blocks"); do
  order=$(printf 'main\ncancel\ntoken\n' | shuf | tr '\n' ' ')
  for v in $order; do
    load=$(cut --delimiter=' ' --fields=1 /proc/loadavg)
    bin=$v extra=
    if [ "$v" = token ]; then bin=cancel extra=cancelon=none; fi
    p50=$(taskset --cpu-list "$ccpu" out/bench/net-client-$bin call GET "http://127.0.0.1:$port/ok" repeat="$calls" trace=0 $extra \
      | sed --quiet 's/^summary later calls .* p50=\([0-9.]*\) .*/\1/p')
    echo "block=$b variant=$v p50_ms=$p50 load=$load"
  done
done
