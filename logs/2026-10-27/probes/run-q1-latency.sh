#!/usr/bin/env bash
# On the box.  ./run-q1-latency.sh  -> out/q1-latency.txt
cd "$HOME/lean-http-probes" || exit 1
for scen in data fin rst none; do
  ./ctr.sh sh -c 'scen=$1; port=$((20000 + RANDOM % 20000)); /py/bin/python3 -I srv1.py $port $scen 10 200 8 > /tmp/s 2>&1 & sleep 0.5; echo "### latency scenario=$scen"; ./bin/idle $port latency 100 200' sh $scen
done > out/q1-latency.txt 2>&1
