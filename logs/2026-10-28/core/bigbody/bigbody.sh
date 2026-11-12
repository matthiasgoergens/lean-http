#!/usr/bin/env bash
# Times GETs of a large Content-Length body through net-client binaries, inside the container of
# scripts/remote.sh, against tests/net/evil.py's bigbody endpoint.  The binaries take turns, in an
# order that alternates from round to round.
# Usage: bash out/bigbody.sh <bytes> <rounds> <binary...>
n=$1; rounds=$2; shift 2
/py/bin/python3 -I tests/net/evil.py --port 18090 > /tmp/evil.log 2>&1 &
server=$!
trap 'kill $server' EXIT
for _ in $(seq 100); do grep --quiet listening /tmp/evil.log && break; sleep 0.05; done
bins=("$@")
for round in $(seq "$rounds"); do
  order=("${bins[@]}")
  if [ $((round % 2)) -eq 0 ]; then order=($(printf '%s\n' "${bins[@]}" | tac)); fi
  for bin in "${order[@]}"; do
    echo "round $round $bin: $("$bin" call GET "http://127.0.0.1:18090/bigbody?n=$n" maxbody=70000000 | grep '^call 0' | cut --delimiter=' ' --fields=1-6)"
  done
done
