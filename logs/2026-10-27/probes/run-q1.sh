#!/usr/bin/env bash
# Inside the container (cwd /w).  Usage: ./run-q1.sh <scenario> <mode> [client_delay_ms] [port]
scen=$1; mode=$2; cd_ms=${3:-400}; port=${4:-$((20000 + RANDOM % 20000))}
/py/bin/python3 -I srv1.py "$port" "$scen" 50 1 6 > /tmp/srv.$$ 2>&1 &
sp=$!
sleep 0.5
echo "### scenario=$scen mode=$mode client_delay=${cd_ms}ms (server acts 50 ms after the exchange)"
timeout 20 ./bin/idle "$port" "$mode" "$cd_ms"; echo "client exit=$?"
sleep 0.2; sed 's/^/  [server] /' /tmp/srv.$$
kill $sp 2>/dev/null
