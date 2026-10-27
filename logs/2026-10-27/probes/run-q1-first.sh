#!/usr/bin/env bash
# Inside the container.  ./run-q1-first.sh <scenario> <n> <client_delay_ms>
scen=$1; n=$2; d=$3; port=$((20000 + RANDOM % 20000))
/py/bin/python3 -I srv1.py "$port" "$scen" 10 "$n" 4 > /tmp/srv.$$ 2>&1 &
sleep 0.5
echo "### first-call scenario=$scen n=$n"
timeout 120 ./bin/idle "$port" first "$d" "$n"; echo "client exit=$?"
