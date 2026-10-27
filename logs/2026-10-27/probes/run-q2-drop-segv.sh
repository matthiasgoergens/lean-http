#!/usr/bin/env bash
# On the box.  ./run-q2-drop-segv.sh <reps> <variant>  -> out/q2-segv/*.txt ; runs with segv.so preloaded
cd "$HOME/lean-http-probes" || exit 1
reps=$1; variant=$2; d=out/q2-segv; mkdir -p $d
[ -f segv.so ] || ./ctr.sh gcc -shared -fPIC -O1 -o segv.so segv.c || exit 1
for r in $(seq $reps); do echo $r; done | xargs -P 4 -L 1 bash -c 'r=$0; CTR_EXTRA="-e LD_PRELOAD=/w/segv.so" ./ctr.sh ./run-q2.sh flood 300 65536 '$variant' 0 300 1 8 > '$d'/flood-'$variant'-r$r.txt 2>&1'
grep -l "fatal signal" $d/*.txt
