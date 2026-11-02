blocks=$1 calls=$2; shift 2; variants="$*"
PY=/py/bin/python3; port=18297
taskset --cpu-list 100 "$PY" -I tests/net/evil.py --port $port > out/bench/abl-server.log 2>&1 &
server=$!; trap 'kill $server' EXIT; sleep 1
for b in $(seq 1 "$blocks"); do
  for v in $(printf '%s\n' $variants | shuf); do
    p50=$(taskset --cpu-list 101 out/bench/net-client-$v call GET "http://127.0.0.1:$port/ok" repeat="$calls" trace=0 | sed --quiet 's/^summary later calls .* p50=\([0-9.]*\) .*/\1/p')
    echo "block=$b variant=$v p50_ms=$p50 load=$(cut -d' ' -f1 /proc/loadavg)"
  done
done
