# The tls-hang call (two 500 ms handshake timeouts and one backoff of 15 ms, seed 1) ROUNDS times
# against a server that never answers the handshake, with HAMMER threads of the client starting and
# stopping timers of the event loop, and HOGS busy loops pinned to CPU, to which the client pins its
# event loop's thread (pinloop=CPU) when HOGS > 0.  Prints each call's time (at least 1015 ms for a
# client whose timeouts never end early: two 500 ms handshakes and the 15 ms backoff) and the gap
# between the server's two accepts (at least the first handshake's 500 ms and the backoff).
# In the build container, from the tree's root, after tests/net/run.sh has made the certificates:
#   bash repro-hs.sh ROUNDS HAMMER CPU HOGS
rounds=$1 hammer=$2 cpu=$3 hogs=$4
PY=/py/bin/python3
certs=out/net/tls-certs
mkdir --parents out/repro
"$PY" -I tests/net/tls.py --cert $certs/good.pem --key $certs/good.key --port 18250 --plain-port 18251 --mode hang > out/repro/tls.log 2>&1 &
server=$!
sleep 1
echo "loadavg $(cat /proc/loadavg) rounds=$rounds hammer=$hammer cpu=$cpu hogs=$hogs"
pin=()
[ "$hogs" -gt 0 ] && pin=(pinloop="$cpu")
early=0
for i in $(seq "$rounds"); do
  pids=()
  for _ in $(seq "$hogs"); do taskset --cpu-list "$cpu" bash -c 'while :; do :; done' & pids+=($!); done
  before=$(grep --count 'accepted from' out/repro/tls.log)
  timeout 60 .lake/build/bin/net-client call GET https://127.0.0.1:18250/hello ca=$certs/ca.pem tlshs=500 retries=1 seed=1 hammer="$hammer" "${pin[@]}" trace=0 > out/repro/call.txt 2>&1
  [ ${#pids[@]} -gt 0 ] && { kill "${pids[@]}" 2>/dev/null; wait "${pids[@]}" 2>/dev/null; }
  ms=$(sed --quiet 's/^call 0 .* ms=\([0-9]*\)\..*/\1/p' out/repro/call.txt)
  gap=$(grep 'accepted from' out/repro/tls.log | tail --lines=+$((before + 1)) | awk 'NR == 1 {a = $1} NR == 2 {printf "%d", $1 - a}')
  flag=""; if [ -n "$ms" ] && [ "$ms" -lt 1012 ]; then flag=" EARLY"; early=$((early + 1)); fi
  echo "round $i: ms=${ms:-?} accept_gap=${gap:-?}$flag $(grep --only-matching 'cause="[^"]*"' out/repro/call.txt) $(grep --max-count=1 --only-matching 'pinned.*\|no thread.*\|taskset failed.*' out/repro/call.txt)"
done
echo "early (under 1012 ms): $early of $rounds"
kill $server
