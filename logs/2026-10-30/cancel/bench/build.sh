#!/usr/bin/env bash
# Builds net-client of main (27a0d86) and of this branch's HEAD on the build host, each in a
# directory of its own from `git archive`, and copies both binaries to ~/lean-http-cancel/out/bench/
# with their SHA-256.  Usage: build.sh
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
host=$(head -n 1 "$root/.build-host")
ctr() { # ctr <dir> <command>
  ssh "$host" "cd ~/$1 && batchrun podman --cgroup-manager=cgroupfs run --cgroups=disabled --rm --network none -v b8perf-elan:/root/.elan:ro -v \"\$PWD\":/w -w /w localhost/b8perf-lean env PATH=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin:/usr/local/bin:/usr/bin:/bin bash -c '$2'"
}
for pair in "main:27a0d86" "cancel:HEAD"; do
  name=${pair%%:*} rev=${pair#*:}
  tree=$(mktemp --directory)
  git -C "$root" archive "$rev" | tar --extract --directory "$tree"
  cp -r "$root/vendor" "$tree/vendor"
  rsync --archive --delete --exclude .lake "$tree/" "$host:lean-http-cancel-bench-$name/" || exit 1
  rm --recursive --force "$tree"
  echo "### $name = $(git -C "$root" rev-parse --short "$rev")"
  ctr "lean-http-cancel-bench-$name" 'lake build net-client 2>&1 | tail -1' || exit 1
  ssh "$host" "mkdir -p ~/lean-http-cancel/out/bench && cp ~/lean-http-cancel-bench-$name/.lake/build/bin/net-client ~/lean-http-cancel/out/bench/net-client-$name && sha256sum ~/lean-http-cancel/out/bench/net-client-$name" || exit 1
done
