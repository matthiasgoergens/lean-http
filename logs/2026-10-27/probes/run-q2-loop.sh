#!/usr/bin/env bash
# On the box.  ./run-q2-loop.sh <reps>  -> out/q2-loop/*.txt, out/q2-loop-summary.txt
# Body-reader style loops over a flooding server (data keeps arriving; main returns at 300 ms).
cd "$HOME/lean-http-probes" || exit 1
reps=$1; d=out/q2-loop; mkdir -p $d
for variant in bgloop mybgloop closeloop; do for r in $(seq $reps); do echo "$variant $r"; done; done | shuf |
 xargs -P 4 -L 1 bash -c 'variant=$0; r=$1; ./ctr.sh ./run-q2.sh flood 0 65536 $variant 0 300 1 8 > '$d'/flood-$variant-r$r.txt 2>&1'
grep -H "exit=" $d/*.txt | sed "s#$d/##" > out/q2-loop-summary.txt
