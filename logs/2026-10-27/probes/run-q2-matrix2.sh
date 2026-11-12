#!/usr/bin/env bash
# On the box.  ./run-q2-matrix2.sh <reps>  -> out/q2-matrix2/<cell>.txt and out/q2-matrix2-summary.txt
# Finer sweep around the race (server acts 290..310 ms after the ping, main returns/closes at 300 ms
# after the exchange), for the library variants.  4 runs at a time, random order, 8 s hang limit.
cd "$HOME/lean-http-probes" || exit 1
reps=$1; d=out/q2-matrix2; mkdir -p $d
for smode_size in "flood 65536" "data 1000" "fin 0"; do
 set -- $smode_size; smode=$1; size=$2
 for sdelay in 290 295 300 305 310; do
  for variant in bg bgcancel mybg mycancel closeable; do
   for r in $(seq $reps); do echo "$smode $size $sdelay $variant $r"; done
  done
 done
done | shuf | xargs -P 4 -L 1 bash -c 'smode=$0; size=$1; sdelay=$2; variant=$3; r=$4
  ./ctr.sh ./run-q2.sh $smode $sdelay $size $variant 0 300 1 8 > '$d'/$smode-$size-d$sdelay-$variant-r$r.txt 2>&1'
grep -H "exit=" $d/*.txt | sed "s#$d/##" > out/q2-matrix2-summary.txt
