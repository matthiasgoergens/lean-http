#!/usr/bin/env bash
# Runs a command in the AFL++ image on the build host, in the tree that scripts/remote.sh keeps
# there (~/$LEAN_HTTP_REMOTE_DIR), with the Lean toolchain mounted read-only, uv's CPython at /py
# (as in scripts/remote.sh) and no network.
# First syncs the tree and builds the harness's C and the replay tool in the Lean image
# (scripts/remote.sh lake build Fuzz fuzz-replay), unless SKIP_LEAN_BUILD=1.
#
# PIN_CPUS pins the container to a CPU list with taskset (rootless podman on the host cannot use
# --cpuset-cpus); CTR_EXTRA adds podman options (for example -d --name ... to detach a campaign).
# The image sets AFL_TRY_AFFINITY, with which afl-fuzz binds itself to a CPU of its choice, outside
# the list, even with AFL_NO_AFFINITY; it is unset here.
#
# Usage: fuzz/run.sh <command> [args...]
#   e.g. fuzz/run.sh fuzz/build.sh
#        fuzz/run.sh fuzz/fuzz.sh .lake/fuzz/campaigns/try 600
# SKIP_LEAN_BUILD=1 also skips the sync: run scripts/remote.sh true first if the tree changed.
host=${LEAN_HTTP_HOST:-buildhost}
rdir=${LEAN_HTTP_REMOTE_DIR:-lean-http}
here=$(cd "$(dirname "$0")/.." && pwd) || exit 1
py=/home/matthias/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu
# AFL++ 5.04a, pinned by digest.
image=docker.io/aflplusplus/aflplusplus@sha256:cb8e839b4b4ec0447aa4ae5c6b1d70811d7704cd32f732695908f84301bbf8ac
if [ "${SKIP_LEAN_BUILD:-0}" != 1 ]; then
  "$here/scripts/remote.sh" lake build Fuzz fuzz-replay >&2 || exit 1
fi
quoted=$(printf '%q ' "$@")
pin=${PIN_CPUS:+taskset --cpu-list $PIN_CPUS}
ssh "$host" "cd ~/$rdir && $pin nice ionice podman run --rm --network none ${CTR_EXTRA:-} \
  -v b8perf-elan:/root/.elan:ro -v \"\$PWD\":/w -w /w -v $py:/py:ro $image \
  env -u AFL_TRY_AFFINITY AFL_SKIP_CPUFREQ=1 AFL_NO_AFFINITY=1 AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES=1 \
  LEAN_ABORT_ON_PANIC=1 LEAN_BACKTRACE=0 $quoted"
