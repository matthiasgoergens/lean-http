#!/usr/bin/env bash
# Randomised blocks: main's Client.request against this branch's Client.request (now read through
# the body stream) and this branch's withResponse read in 64 KiB pulls, each on a 60 MB body from
# evil.py over loopback.  Runs inside the container (scripts/remote.sh), from the branch's tree, with
# main's net-client at /main/net-client.
#
# Usage: bash bench-bigbody.sh <out> <blocks> <seed>
out=${1:?out}; blocks=${2:-20}; seed=${3:-1}
PY=/py/bin/python3
wire=/w/.lake/build/bin/net-client
main=/main/net-client
sha256sum "$main" "$wire" > "$out" || exit 1
taskset --cpu-list 100 "$PY" -I /w/tests/net/evil.py --port 18150 > /tmp/bench-evil.log 2>&1 &
srv=$!
trap 'kill $srv' EXIT
for _ in $(seq 100); do grep --quiet listening /tmp/bench-evil.log && break; sleep 0.05; done
url="http://127.0.0.1:18150/bigbody?n=60000000"
RANDOM=$seed
for b in $(seq 1 "$blocks"); do
  cells=(main wire stream)
  # Fisher-Yates shuffle of the three cells
  for i in 2 1; do j=$((RANDOM % (i + 1))); t=${cells[$i]}; cells[$i]=${cells[$j]}; cells[$j]=$t; done
  for c in "${cells[@]}"; do
    case $c in
      main) line=$(taskset --cpu-list 101 "$main" call GET "$url" repeat=5 maxbody=100000000 | grep '^summary calls') ;;
      wire) line=$(taskset --cpu-list 101 "$wire" call GET "$url" repeat=5 maxbody=100000000 trace=0 | grep '^summary calls') ;;
      stream) line=$(taskset --cpu-list 101 "$wire" stream GET "$url" repeat=5 pull=65536 trace=0 | grep '^stream ' | sed 's/.* ms=\([0-9.]*\) .*/\1/' | sort -n | sed -n 3p) ;;
    esac
    echo "block=$b cell=$c $line" >> "$out"
  done
done
echo done >> "$out"
