#!/usr/bin/env bash
# Runs inside the container at the tree's root, with this file, core-run.sh and the replays in out/:
# a full build, the axioms, the pure suites (core-run.sh) and the counterexample replays.
# Usage: bash out/run-all.sh <tag>
tag=${1:?tag}
mkdir --parents "out/$tag" || exit 1
{ echo '$ lake build'; lake build; echo "exit status $?"; } > "out/$tag/build.txt" 2>&1
{ echo '$ lake env lean scripts/proof-axioms.lean'; lake env lean scripts/proof-axioms.lean
  echo "exit status $?"; } > "out/$tag/axioms.txt" 2>&1
bash out/core-run.sh "$tag"
bash out/run.sh > "out/$tag/replays.txt" 2>&1
echo "replays: exit status $?"
