#!/usr/bin/env bash
# On the box: ~/lean-http-probes/run-q1-all.sh   (raw output -> out/q1-all.txt)
cd "$HOME/lean-http-probes" || exit 1
mkdir -p out
for scen in data fin rst none; do
  for mode in once loop spaced wait ready; do
    ./ctr.sh ./run-q1.sh $scen $mode 400
  done
done > out/q1-all.txt 2>&1
