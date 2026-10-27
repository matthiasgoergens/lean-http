#!/usr/bin/env bash
cd "$HOME/lean-http-probes" || exit 1
mkdir -p out
for d in 100 1000; do for scen in data fin rst none; do ./ctr.sh ./run-q1-first.sh $scen 100 $d; done; done > out/q1-first.txt 2>&1
