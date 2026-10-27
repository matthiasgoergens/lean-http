#!/usr/bin/env bash
# On the box.  ./run-q2-matrix.sh <reps>   -> out/q2-matrix/<cell>-r<k>.txt and out/q2-matrix-summary.txt
# Cells: server mode/size/delay x client variant (hold 300 ms), run 4 at a time, in random order.
cd "$HOME/lean-http-probes" || exit 1
reps=$1; d=out/q2-matrix; mkdir -p $d
for smode_size in "data 1000" "data 1048576" "data 67108864" "fin 0" "rst 0" "flood 65536"; do
 set -- $smode_size; smode=$1; size=$2
 for sdelay in 0 150 290 300 310 450; do
  for variant in bg bgcancel bgshut; do
   for r in $(seq $reps); do
    echo "$smode $size $sdelay $variant $r"
   done
  done
 done
done | shuf | xargs -P 4 -L 1 bash -c 'smode=$0; size=$1; sdelay=$2; variant=$3; r=$4
  ./ctr.sh ./run-q2.sh $smode $sdelay $size $variant 0 300 1 8 > '$d'/$smode-$size-d$sdelay-$variant-r$r.txt 2>&1'
grep -H "exit=" $d/*.txt | sed "s#$d/##" > out/q2-matrix-summary.txt
