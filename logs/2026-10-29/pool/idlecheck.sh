#!/usr/bin/env bash
# Runs net-client idlecheck for each scenario and window against tests/net/idle.py, inside the
# container.  Usage: bash idlecheck.sh <outfile> <n>
outf=${1:?outfile}; n=${2:-200}
/py/bin/python3 -I /w/tests/net/idle.py 18102 > /tmp/idle.log 2>&1 &
srv=$!
for _ in $(seq 100); do grep --quiet listening /tmp/idle.log && break; sleep 0.05; done
{
  echo "### $(date --utc +%FT%TZ) load: $(cat /proc/loadavg)"
  for ms in 0 1 2 5; do
    for sc in data fin rst none; do
      echo "\$ net-client idlecheck 18102 scenario=$sc ms=$ms n=$n"
      /w/.lake/build/bin/net-client idlecheck 18102 scenario=$sc ms=$ms n=$n
    done
  done
  echo "### load after: $(cat /proc/loadavg)"
} > "$outf" 2>&1
kill $srv
