#!/usr/bin/env bash
# Inside the container: the random runs with the generator's empty reads taken out again
# (no-empty-reads.diff), to compare with the runs before the change on the same core events.
lake build core-tests 2>&1 | tail -n 1
for s in 1 2; do
  { echo "\$ core-tests props 200000 $s"; .lake/build/bin/core-tests props 200000 $s; echo "exit status $?"; } > out/no-empty-$s.txt 2>&1
done
