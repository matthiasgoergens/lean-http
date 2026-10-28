#!/usr/bin/env bash
# Positive controls: for each planted bug, copies the tree (without .git) to a scratch directory,
# plants the bug (plant.py), builds core-tests on the build host in a directory of its own, and runs
# the traces, the random runs and the explorer.  For head-before-write it also runs the random runs
# and the explorer without the property that catches it first, to show that the head property
# catches it on its own.  Writes <name>.diff and <name>.txt next to this script.
#   bash logs/2026-10-28/core/planted/run.sh [name...]
here=$(cd "$(dirname "$0")" && pwd) || exit 1
repo=$(cd "$here/../../../.." && pwd) || exit 1
names=${*:-head-before-write two-writes reuse-with-leftovers not-sent-while-writing}
for name in $names; do
  scratch=$(mktemp --directory) || exit 1
  rsync --archive --exclude .git --exclude .lake --exclude logs --exclude out "$repo/" "$scratch/" || exit 1
  "$here/plant.py" "$scratch" "$name" || exit 1
  diff --unified "$repo/LeanHttp/Exchange.lean" "$scratch/LeanHttp/Exchange.lean" \
    | sed -e "s|$repo/||" -e "s|$scratch/||" > "$here/$name.diff"
  extra=()
  if [ "$name" = head-before-write ]; then
    extra=("props 200000 1 --skip 'unsolicited bytes fail the exchange'"
           "explore 10 --skip 'unsolicited bytes fail the exchange'")
  fi
  {
    echo 'lake build core-tests 2>&1 | grep -v "^✔" | tail -3'
    for c in "traces" "props 200000 1" "explore 10" "${extra[@]}"; do
      echo "echo '### core-tests $(printf '%s' "$c" | sed "s/'/'\\\\''/g")'"
      echo ".lake/build/bin/core-tests $c; echo \"exit status \$?\""
    done
  } > "$scratch/controls.sh"
  out=$here/$name.txt
  {
    echo "# planted bug: $name (diff in $name.diff), on $(git -C "$repo" rev-parse --short HEAD)"
    echo "# LEAN_HTTP_REMOTE_DIR=lean-http-core-planted scripts/remote.sh bash controls.sh, where controls.sh is:"
    sed 's/^/#   /' "$scratch/controls.sh"
    LEAN_HTTP_REMOTE_DIR=lean-http-core-planted "$scratch/scripts/remote.sh" bash controls.sh
  } > "$out" 2>&1
  rm --recursive --force "$scratch"
  echo "$name: $(grep --count '^exit status 1' "$out") of $(grep --count '^exit status' "$out") checks failed"
done
