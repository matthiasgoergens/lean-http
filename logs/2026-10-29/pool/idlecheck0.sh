#!/usr/bin/env bash
# The idle check with a window of 0 ms, 1000 fresh connections per scenario, against
# tests/net/idle.py, inside the container.  Usage: bash idlecheck0.sh <outfile>
outf=${1:?outfile}
/py/bin/python3 -I /w/tests/net/idle.py 18103 > /tmp/idle0.log 2>&1 &
srv=$!
for _ in $(seq 100); do grep --quiet listening /tmp/idle0.log && break; sleep 0.05; done
{
  echo "### $(date --utc +%FT%TZ) load: $(cat /proc/loadavg)"
  for sc in data fin rst none; do
    echo "\$ net-client idlecheck 18103 scenario=$sc ms=0 n=1000"
    /w/.lake/build/bin/net-client idlecheck 18103 scenario=$sc ms=0 n=1000
  done
  echo "### load after: $(cat /proc/loadavg)"
} > "$outf" 2>&1
kill $srv
