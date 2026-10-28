#!/usr/bin/env bash
# Groups a campaign's crashes and hangs by the invariant they break (fuzz-replay --class) and
# minimises the first input of each class with afl-tmin, keeping the minimised input only if it
# breaks the same invariant.  Writes <campaign>/triage/: classes.txt (count, class, example) and
# min/<n>.bin with min/<n>.txt (the replay of the minimised input).
#
# Runs inside the AFL++ image (fuzz/run.sh), in the tree, after fuzz/build.sh.
#
# Usage: fuzz/triage.sh <campaign dir>
dir=${1:?campaign dir}
bin=.lake/fuzz/plain/lean-http-fuzz
replay=.lake/build/bin/fuzz-replay
out=$dir/triage
rm --recursive --force "$out" && mkdir --parents "$out/min" || exit 1
: > "$out/all.tsv"
for f in "$dir"/sync/*/crashes/id* "$dir"/sync/*/hangs/id*; do
  [ -f "$f" ] || continue
  # A hang that the replay tool finishes is reported as such; one it does not finish in 10 s is a
  # real endless loop.
  cls=$(timeout 10 "$replay" --class "$f" | head --lines=1)
  [ -n "$cls" ] || cls="replay did not finish within 10 s"
  printf '%s\t%s\n' "$cls" "$f" >> "$out/all.tsv"
done
cut --fields=1 "$out/all.tsv" | sort | uniq --count | sort --reverse --numeric-sort > "$out/counts.txt"
n=0
: > "$out/classes.txt"
while read -r count cls; do
  n=$((n + 1))
  ex=$(awk -F '\t' -v c="$cls" '$1 == c { print $2; exit }' "$out/all.tsv")
  printf '%s\t%s\t%s\t%s\n' "$n" "$count" "$cls" "$ex" >> "$out/classes.txt"
  cp "$ex" "$out/min/$n.orig" || exit 1
  if [ "$cls" != ok ] && afl-tmin -i "$ex" -o "$out/min/$n.bin" -- "$bin" > "$out/min/$n.tmin.log" 2>&1 \
     && [ "$(timeout 10 "$replay" --class "$out/min/$n.bin" | head --lines=1)" = "$cls" ]; then
    :
  else
    cp "$ex" "$out/min/$n.bin" || exit 1
  fi
  timeout 10 "$replay" "$out/min/$n.bin" > "$out/min/$n.txt" 2>&1
done < <(sed -E 's/^ *([0-9]+) (.*)$/\1 \2/' "$out/counts.txt")
cat "$out/classes.txt"
