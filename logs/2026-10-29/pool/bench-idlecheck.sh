#!/usr/bin/env bash
# Times reused calls with the idle check off and with windows of 0, 1 and 5 ms, in randomised
# blocks: each block runs every cell once, in an order drawn per block.  A cell is one run of
# net-client making 51 GET calls one after another through one client to evil.py's /ok (the first
# opens the connection, the other 50 reuse it); its result is the median of those 50.  The server
# runs pinned to CPU 100, the client to CPU 101.  Runs inside the container (scripts/remote.sh).
#
# Usage: bash bench-idlecheck.sh <outfile> <blocks> <seed>
outf=${1:?outfile}; blocks=${2:-20}; seed=${3:-1}
taskset --cpu-list 100 /py/bin/python3 -I /w/tests/net/evil.py --port 18110 > /tmp/bench-evil.log 2>&1 &
srv=$!
for _ in $(seq 100); do grep --quiet listening /tmp/bench-evil.log && break; sleep 0.05; done
cells=(off 0 1 5)
RANDOM=$seed
{
  echo "### $(date --utc +%FT%TZ) blocks=$blocks seed=$seed load: $(cat /proc/loadavg)"
  sha256sum /w/.lake/build/bin/net-client
  echo "block cell later_p50_ms check_p50_ms"
  for b in $(seq 1 "$blocks"); do
    order=("${cells[@]}")
    for i in 3 2 1; do j=$((RANDOM % (i + 1))); t=${order[$i]}; order[$i]=${order[$j]}; order[$j]=$t; done
    for c in "${order[@]}"; do
      res=$(taskset --cpu-list 101 /w/.lake/build/bin/net-client call GET http://127.0.0.1:18110/ok repeat=51 idlecheck=$c)
      later=$(echo "$res" | sed --quiet 's/^summary later calls n=50 .* p50=\([0-9.]*\) .*/\1/p')
      check=$(echo "$res" | sed --quiet 's/^summary idle checks of reused connections n=[0-9]* .* p50=\([0-9.]*\) .*/\1/p')
      echo "$b $c ${later:-?} ${check:--}"
    done
  done
  echo "### load after: $(cat /proc/loadavg)"
} > "$outf" 2>&1
kill $srv
