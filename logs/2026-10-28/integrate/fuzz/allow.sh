#!/usr/bin/env bash
# Counts, per corpus, the cross-check allowances the inputs rely on (fuzz-replay --allowances).
for set in seeds cmin old-inputs main2; do
  find "out/corpus/$set" -type f ! -name README.txt ! -path '*/.state/*' -print0 | sort --zero-terminated \
    | xargs --null --max-args=500 .lake/build/bin/fuzz-replay --allowances > "out/replay/$set-allowances.txt"
  echo "== $set"
  sort "out/replay/$set-allowances.txt" | uniq --count | sort --reverse --numeric-sort
done
