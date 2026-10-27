#!/usr/bin/env bash
# Run a command inside a throwaway container (image localhost/b8perf-lean, Lean v4.34.1 from the
# b8perf-elan volume, read-only), no network (loopback only), this directory at /w, uv's CPython
# 3.14 at /py (read-only).  Usage on the build host: ~/lean-http-probes/ctr.sh <command...>
base=$HOME/lean-http-probes
exec podman run --rm --network=none ${CTR_EXTRA:-} \
  -v b8perf-elan:/root/.elan:ro \
  -v "$base":/w:Z \
  -v "$HOME/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu":/py:ro \
  -w /w localhost/b8perf-lean env PATH=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin:/usr/local/bin:/usr/bin:/bin "$@"
