#!/usr/bin/env bash
# Replays every input of the copied corpora through fuzz-replay --class; writes out/replay/<set>.txt
# (one class per file) and prints a count per class.  Run inside the container from the tree.
mkdir --parents out/replay || exit 1
for set in seeds cmin old-inputs main2; do
  find "out/corpus/$set" -type f ! -name README.txt ! -path '*/.state/*' -print0 | sort --zero-terminated \
    | xargs --null --max-args=500 .lake/build/bin/fuzz-replay --class > "out/replay/$set.txt"
  echo "== $set: $(wc --lines < "out/replay/$set.txt") files"
  sort "out/replay/$set.txt" | uniq --count | sort --reverse --numeric-sort
done
