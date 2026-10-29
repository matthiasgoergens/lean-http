#!/usr/bin/env bash
# Runs the container through batchrun, below CI and interactive work on the host, with Podman kept in
# the batch service's cgroup.  Copies the working tree to ~/$LEAN_HTTP_REMOTE_DIR (default ~/lean-http) on the build host and runs a command there, inside the
# Lean image with the v4.34.1 toolchain from the b8perf-elan volume (read-only), the tree at /w,
# uv's CPython at /py, and no network but loopback.  CTR_EXTRA adds podman options.
#
# Usage: scripts/remote.sh <command> [args...]
#   e.g. scripts/remote.sh lake build
#        scripts/remote.sh bash tests/net/run.sh all
# The build host: $LEAN_HTTP_HOST, else the first line of an untracked .build-host file at the root.
host=${LEAN_HTTP_HOST:-$(head -n 1 "$(dirname "$0")/../.build-host" 2>/dev/null)}
[ -n "$host" ] || { echo "set LEAN_HTTP_HOST, or put the build host's ssh name in .build-host" >&2; exit 1; }
# The directory on the host; give each worktree its own, so that parallel runs do not share a tree.
rdir=${LEAN_HTTP_REMOTE_DIR:-lean-http}
here=$(cd "$(dirname "$0")/.." && pwd) || exit 1
py=/home/matthias/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu
# The vendored protocol layer is generated, not committed: make it if it is missing or stale.
commit=$(sed --quiet 's/^commit=//p' "$here/scripts/vendor.sh")
grep --quiet --fixed-strings "$commit" "$here/vendor/SOURCE" 2>/dev/null \
  || "$here/scripts/vendor.sh" >&2 || exit 1
rsync --archive --delete --exclude .lake --exclude .git --exclude logs --exclude out \
  "$here/" "$host:$rdir/" || exit 1
quoted=$(printf '%q ' "$@")
ssh "$host" "cd ~/$rdir && batchrun podman --cgroup-manager=cgroupfs run --cgroups=disabled --rm --network none ${CTR_EXTRA:-} \
  -v b8perf-elan:/root/.elan:ro -v \"\$PWD\":/w -w /w -v $py:/py:ro localhost/b8perf-lean \
  env PATH=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin:/usr/local/bin:/usr/bin:/bin $quoted"
