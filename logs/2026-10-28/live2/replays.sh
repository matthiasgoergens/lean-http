#!/usr/bin/env bash
# Runs inside the container at the tree's root, with the replays copied to out/.
lake build TestSupport 2>&1 | tail -n 1
for f in out/gap0.lean out/zero.lean out/clock.lean; do
  if [ "$f" = out/zero.lean ]; then echo "\$ lake env lean $f"; else echo "\$ lake env lean --run $f"; fi
  if [ "$f" = out/zero.lean ]; then lake env lean "$f"; else lake env lean --run "$f"; fi
  echo "exit status $?"
done
