#!/usr/bin/env bash
# Inside the container.  ./run-prom.sh <variant> <main_ms> <resolve_ms> [limit_s]
limit=${4:-6}
echo "### prom variant=$1 main=${2}ms resolve=${3}ms"
t0=$(date +%s%N)
timeout --signal=KILL "$limit" ./bin/prom "$1" "$2" "$3" 2>&1 | sed 's/^/  /'
st=${PIPESTATUS[0]}
echo "  exit=$st wall=$(( ($(date +%s%N) - t0) / 1000000 ))ms $([ "$st" = 137 ] && echo HANG-killed-at-limit)"
