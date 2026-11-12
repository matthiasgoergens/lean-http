#!/usr/bin/env bash
# Inside the container (cwd /w).
# ./run-q2.sh <server-mode> <server-delay-ms> <size> <variant> <arg-ms> <hold-ms> [n] [limit-s]
# Prints client output, exit status (124 = still running at the limit = hang), wall time.
smode=$1; sdelay=$2; size=$3; variant=$4; argms=$5; hold=$6; n=${7:-1}; limit=${8:-10}
port=$((20000 + RANDOM % 20000))
nconns=$n; [ "$variant" = bg2 ] && nconns=2
/py/bin/python3 -I srv2.py "$port" "$smode" "$sdelay" "$size" "$nconns" 30 > /tmp/srv.$$ 2>&1 &
sp=$!
sleep 0.3
echo "### server=$smode delay=${sdelay}ms size=$size | client variant=$variant arg=${argms}ms hold=${hold}ms n=$n"
t0=$(date +%s%N)
timeout --signal=KILL "$limit" ./bin/hang "$port" "$variant" "$argms" "$hold" "$n" 2>&1 | sed 's/^/  [client] /'
st=${PIPESTATUS[0]}
t1=$(date +%s%N)
echo "  exit=$st wall=$(( (t1 - t0) / 1000000 ))ms $([ "$st" = 137 ] && echo HANG-killed-at-limit)"
sed 's/^/  [server] /' /tmp/srv.$$ | head -5
kill $sp 2>/dev/null
