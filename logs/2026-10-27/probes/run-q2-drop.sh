#!/usr/bin/env bash
# On the box.  ./run-q2-drop.sh <reps> <variant>  -> out/q2-drop2/*.txt, out/q2-drop2-summary.txt
# <variant> abandoned while a flood streams in and main returns at the same moment as the server acts (300 ms).
cd "$HOME/lean-http-probes" || exit 1
reps=$1; variant=$2; d=out/q2-drop2; mkdir -p $d
for r in $(seq $reps); do echo $r; done | xargs -P 6 -L 1 bash -c 'r=$0; ./ctr.sh ./run-q2.sh flood 300 65536 '$variant' 0 300 1 8 > '$d'/flood-'$variant'-r$r.txt 2>&1'
grep -H "exit=" $d/flood-$variant-*.txt | sed "s#$d/##" > out/q2-drop2-$variant-summary.txt
