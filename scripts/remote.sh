#!/usr/bin/env bash
# Copies the working tree to ~/lean-http on the build host and runs a command there, inside the
# Lean image with the v4.34.1 toolchain from the b8perf-elan volume (read-only), the tree at /w,
# uv's CPython at /py, and no network but loopback.  CTR_EXTRA adds podman options.
#
# Usage: scripts/remote.sh <command> [args...]
#   e.g. scripts/remote.sh lake build
#        scripts/remote.sh bash tests/net/run.sh all
host=${LEAN_HTTP_HOST:-buildhost}
here=$(cd "$(dirname "$0")/.." && pwd) || exit 1
py=/home/matthias/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu
rsync --archive --delete --exclude .lake --exclude .git --exclude logs \
  "$here/" "$host:lean-http/" || exit 1
quoted=$(printf '%q ' "$@")
ssh "$host" "cd ~/lean-http && nice ionice podman run --rm --network none ${CTR_EXTRA:-} \
  -v b8perf-elan:/root/.elan:ro -v \"\$PWD\":/w -w /w -v $py:/py:ro localhost/b8perf-lean \
  env PATH=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin:/usr/local/bin:/usr/bin:/bin $quoted"
