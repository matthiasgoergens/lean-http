#!/usr/bin/env bash
# On the box.  ./run-prom-all.sh  -> out/prom.txt
cd "$HOME/lean-http-probes" || exit 1
for rep in 1 2 3; do
 for v in mapped direct mappedsync mappedjoin; do
  ./ctr.sh ./run-prom.sh $v 50 200   # main returns first
  ./ctr.sh ./run-prom.sh $v 300 100  # promise resolved first
 done
done > out/prom.txt 2>&1
