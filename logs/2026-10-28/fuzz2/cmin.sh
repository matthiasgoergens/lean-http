#!/usr/bin/env bash
# Runs in the AFL++ image (fuzz/run.sh), at the tree's root, after fuzz/build.sh: reduces the old
# campaigns' distinct inputs (out/old-inputs) and the current seeds with afl-cmin against the
# ported harness, into out/cmin, the extra seeds of the campaign.
rm -rf out/cmin out/cmin-in && mkdir --parents out/cmin-in || exit 1
/py/bin/python3 -I fuzz/seeds.py out/cmin-in > /dev/null || exit 1
cp out/old-inputs/* out/cmin-in/ || exit 1
echo "inputs: $(ls out/cmin-in | wc -l)"
AFL_NO_AFFINITY=1 afl-cmin -i out/cmin-in -o out/cmin -t 1000 -- .lake/fuzz/plain/lean-http-fuzz 2>&1 | tail -n 5
echo "kept: $(ls out/cmin | wc -l)"
