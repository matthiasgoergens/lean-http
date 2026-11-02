# Runs the tls-handshake scenarios ROUNDS times with the whole suite pinned to CPUS alongside HOGS busy
# loops there, printing the tls-hang verdicts and the server's accept times of each round.
# In the build container, from the tree's root: bash -c "$(cat repro-tls-hang.sh)" x ROUNDS CPUS HOGS
rounds=$1 cpus=$2 hogs=$3
mkdir --parents out/net
echo "loadavg $(cat /proc/loadavg) rounds=$rounds cpus=$cpus hogs=$hogs"
for i in $(seq "$rounds"); do
  pids=()
  for _ in $(seq "$hogs"); do taskset --cpu-list "$cpus" bash -c 'while :; do :; done' & pids+=($!); done
  taskset --cpu-list "$cpus" bash tests/net/run.sh tls-handshake > out/round.txt 2>&1
  kill "${pids[@]}" 2>/dev/null; wait "${pids[@]}" 2>/dev/null
  echo "=== round $i: $(grep --extended-regexp '^(PASS|FAIL) tls-hang: two' out/round.txt) | $(grep --extended-regexp '^FAIL' out/round.txt | grep --invert-match 'tls-hang: two' | cut --characters=1-200 | tr '\n' ';')"
  grep 'accepted from' out/net/tls-hang.tls.log | awk '{printf "%s ", $1} END {print ""}'
done
