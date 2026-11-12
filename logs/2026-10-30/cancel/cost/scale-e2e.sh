#!/usr/bin/env bash
# Runs inside the build container (scripts/remote.sh), from the repository root, copied to
# out/bench/ first (as blocks.sh): rounds of k concurrent GETs through one client to evil.py's /ok,
# all given one token that is never cancelled (cancelon=none), with net-client of each binary.
# Each block runs every binary once for every k, in random order; each run makes <rounds> rounds of
# k calls and prints the median time of a round.  Server on CPU <server cpu>, client on <client cpus>
# (a taskset list).
# Usage: scale-e2e.sh <blocks> <rounds> <server cpu> <client cpus> <k list, comma-separated> <binary>...
set -u
blocks=$1 rounds=$2 scpu=$3 ccpus=$4 ks=$5; shift 5
PY=${PY:-/py/bin/python3}
port=${PORT:-18351}
log=out/bench/scale-server-$port.log
taskset --cpu-list "$scpu" "$PY" -I tests/net/evil.py --port "$port" > "$log" 2>&1 &
server=$!
trap 'kill $server 2>/dev/null; wait $server 2>/dev/null' EXIT
for _ in $(seq 100); do grep --quiet listening "$log" && break; sleep 0.05; done
for b in "$@"; do sha256sum "out/bench/net-client-$b"; done
for blk in $(seq 1 "$blocks"); do
  for run in $(for k in $(tr , ' ' <<< "$ks"); do for b in "$@"; do echo "$b/$k"; done; done | shuf); do
    b=${run%/*} k=${run#*/}
    load=$(cut --delimiter=' ' --fields=1 /proc/loadavg)
    out=$(taskset --cpu-list "$ccpus" "out/bench/net-client-$b" call GET "http://127.0.0.1:$port/ok" \
      concurrent="$k" repeat="$rounds" trace=0 cancelon=none maxidle="$k")
    med=$(sed --quiet 's/^round [0-9]* of [0-9]* calls took ms=//p' <<< "$out" | sort --numeric-sort \
      | awk '{a[NR]=$1} END {if (NR % 2) print a[(NR+1)/2]; else print (a[NR/2]+a[NR/2+1])/2}')
    oks=$(grep --count ' ok status=200' <<< "$out")
    echo "block=$blk variant=$b k=$k round_ms=$med ok=$oks load=$load"
  done
done
