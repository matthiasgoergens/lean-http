#!/usr/bin/env bash
# Positive controls for the core checker's streamed-body properties: each planted defect
# (mutate.py) on the committed tree (HEAD), built and run on the build host in a directory of its
# own (directly, not through scripts/remote.sh, which would copy the working tree over it).  For each:
# core-tests traces, props 50000 1 and explore 10, and the first failure each reports.
# Usage: run.sh [mutation...]   (default: none, then every mutation)
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
host=$(head -n 1 "$root/.build-host")
ctr() { # ctr <dir> <command>
  ssh "$host" "cd ~/$1 && batchrun podman --cgroup-manager=cgroupfs run --cgroups=disabled --rm --network none -v b8perf-elan:/root/.elan:ro -v \"\$PWD\":/w -w /w -v /home/matthias/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu:/py:ro localhost/b8perf-lean env PATH=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin:/usr/local/bin:/usr/bin:/bin bash -c '$2'"
}
echo "HEAD $(git -C "$root" rev-parse --short HEAD)"
names=("$@")
[ ${#names[@]} -gt 0 ] || names=(none pull-early pull-with-write pull-before-head size-plus-one short-end no-crlf wire-done ignore-broken ignore-failure)
for m in "${names[@]}"; do
  tree=$(mktemp --directory)
  git -C "$root" archive HEAD | tar --extract --directory "$tree"
  cp -r "$root/vendor" "$tree/vendor"
  [ $m = none ] || (cd "$tree" && python3 "$here/mutate.py" $m) || exit 1
  rsync --archive --delete --exclude .lake "$tree/" "$host:lean-http-upload-ctl2/" || exit 1
  rm --recursive --force "$tree"
  echo "### $m"
  ctr lean-http-upload-ctl2 'lake build core-tests 2>&1 | grep -E "error|^Build" | head -3
    for s in "traces" "props 50000 1" "explore 10"; do
      echo "core-tests $s: $(.lake/build/bin/core-tests $s 2>&1 | grep -E "^(FAIL|PASS [0-9]|[0-9]+ (traces|searches))" | head -2 | tr "\n" " " | cut -c1-300)"
    done'
done
