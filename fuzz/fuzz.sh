#!/usr/bin/env bash
# Runs an AFL++ campaign on the harness: one main instance with the comparison-logging build
# (-c) and deterministic mutations (-D), and N-1 secondaries, each for SECONDS, all synchronising
# through OUT/sync.  Seeds come from fuzz/seeds.py, the dictionary from fuzz/http-response.dict.
#
# Runs inside the AFL++ image (fuzz/run.sh), in the tree, after fuzz/build.sh.  Pin it with
# PIN_CPUS on fuzz/run.sh, one CPU per instance; AFL_NO_AFFINITY is set there.
#
# Usage: fuzz/fuzz.sh <out dir> <seconds> [instances (default 1)] [timeout ms (default 200)]
out=${1:?out dir}
secs=${2:?seconds}
n=${3:-1}
tmo=${4:-200}
bin=.lake/fuzz/plain/lean-http-fuzz
cmp=.lake/fuzz/cmplog/lean-http-fuzz
[ -x "$bin" ] && [ -x "$cmp" ] || { echo "fuzz.sh: run fuzz/build.sh first" >&2; exit 1; }
[ ! -e "$out/sync" ] || { echo "fuzz.sh: $out/sync exists; use a fresh directory" >&2; exit 1; }
mkdir --parents "$out" || exit 1
/py/bin/python3 -I fuzz/seeds.py "$out/seeds" || exit 1
# -G: the control byte, 15 split-table entries and Fuzz/Harness.lean's maxResponse (2432 bytes).
common=(-i "$out/seeds" -o "$out/sync" -x fuzz/http-response.dict -t "$tmo" -G 2448 -V "$secs")
{ echo "afl-fuzz $(afl-fuzz -h 2>&1 | head -1)"; sha256sum "$bin" "$cmp"; date --utc; } > "$out/build-info.txt"
export AFL_NO_UI=1
# The main instance also runs the deterministic stage (-D), which tries every single-byte change to
# each new queue entry: AFL++ skips it by default, and without it a one-byte change to a split-table
# entry can go untried for hours.
afl-fuzz -M main -D -c "$cmp" "${common[@]}" -- "$bin" > "$out/main.log" 2>&1 &
pids=($!)
for i in $(seq 2 "$n"); do
  afl-fuzz -S "s$i" "${common[@]}" -- "$bin" > "$out/s$i.log" 2>&1 &
  pids+=($!)
done
status=0
for p in "${pids[@]}"; do wait "$p" || status=1; done
afl-whatsup -s "$out/sync" > "$out/whatsup.txt" 2>&1
exit $status
