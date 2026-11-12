# net-client timers ROUNDS times, with HOGS busy loops pinned to CPU, to which the client pins its
# event loop's thread, and HAMMER threads of the client using the loop.  In the build container,
# from the tree's root: bash repro-timers.sh ROUNDS HAMMER CPU HOGS
rounds=$1 hammer=$2 cpu=$3 hogs=$4
echo "loadavg $(cat /proc/loadavg) rounds=$rounds hammer=$hammer cpu=$cpu hogs=$hogs"
for i in $(seq "$rounds"); do
  pids=()
  for _ in $(seq "$hogs"); do taskset --cpu-list "$cpu" bash -c 'while :; do :; done' & pids+=($!); done
  echo "round $i"
  timeout 120 .lake/build/bin/net-client timers hammer="$hammer" pinloop="$cpu" 2>&1
  [ ${#pids[@]} -gt 0 ] && { kill "${pids[@]}" 2>/dev/null; wait "${pids[@]}" 2>/dev/null; }
done
