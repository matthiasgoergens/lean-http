#!/usr/bin/env bash
# Copies this directory to the build host and runs a command in the Lean container there, under
# batchrun.  Usage: run.sh <command...>
host=$(head -n 1 "$(dirname "$0")/../../../../../.build-host")
here=$(cd "$(dirname "$0")" && pwd)
rsync --archive --exclude .lake "$here/" "$host:lean-http-load-probe/" || exit 1
quoted=$(printf '%q ' "$@")
ssh "$host" "cd ~/lean-http-load-probe && echo loadavg \$(cat /proc/loadavg) && batchrun podman --cgroup-manager=cgroupfs run --cgroups=disabled --rm --network none \
  -v b8perf-elan:/root/.elan:ro -v \"\$PWD\":/w -w /w localhost/b8perf-lean \
  env PATH=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin:/usr/local/bin:/usr/bin:/bin $quoted"
