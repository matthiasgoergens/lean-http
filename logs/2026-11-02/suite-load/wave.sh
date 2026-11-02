#!/usr/bin/env bash
# The stability wave: three copies of the full CI script at once, each RUNS times in a row, one on
# v4.35.0 alongside them, and three copies of rounds.sh, with the build host's load average sampled
# every 15 s.  Run from the worktree's root on the laptop: bash logs/2026-11-02/suite-load/wave.sh RUNS ROUNDS
# Writes logs/2026-11-02/suite-load/{ci-1,ci-2,ci-3}/run-N/, ci-v4.35.0/, rounds-N.txt,
# rounds-failed-N/, loadavg.txt and commit.
runs=${1:-3} rounds=${2:-10}
here=logs/2026-11-02/suite-load
host=$(head -n 1 .build-host)
git rev-parse --short HEAD > "$here/commit"
ssh "$host" 'while :; do echo "$(date --utc +%FT%TZ) $(cat /proc/loadavg)"; sleep 15; done' > "$here/loadavg.txt" &
sampler=$!
ci() { # ci <copy> <run> [env...]
  local d=$1 r=$2; shift 2
  mkdir --parents "$here/$d/$r"
  env "$@" CTR_EXTRA='--sysctl net.ipv4.tcp_syn_retries=2' \
    scripts/remote.sh bash -c 'rm -rf .lake out && lean --version && bash scripts/ci.sh' \
    > "$here/$d/$r/console.txt" 2>&1
  local rdir
  rdir=$(env "$@" bash -c 'echo ${LEAN_HTTP_REMOTE_DIR}')
  rsync --archive --exclude tls-certs "$host:$rdir/out/ci" "$host:$rdir/out/net" "$here/$d/$r/"
}
pids=()
for k in 1 2 3; do
  ( for r in $(seq "$runs"); do ci "ci-$k" "run-$r" LEAN_HTTP_REMOTE_DIR=lean-http-load-$k; done ) & pids+=($!)
done
( ci ci-v4.35.0 . LEAN_HTTP_REMOTE_DIR=lean-http-load-435 LEAN_HTTP_TOOLCHAIN=v4.35.0 LEAN_HTTP_ELAN=b8perf-elan ) & pids+=($!)
for k in 4 5 6; do
  ( CTR_EXTRA='--sysctl net.ipv4.tcp_syn_retries=2' LEAN_HTTP_REMOTE_DIR=lean-http-load-$k \
      scripts/remote.sh bash -c "$(cat "$here/rounds.sh")" rounds.sh "$rounds" > "$here/rounds-$k.txt" 2>&1
    rsync --archive "$host:lean-http-load-$k/out/rounds/" "$here/rounds-failed-$k/" 2>/dev/null ) & pids+=($!)
done
wait "${pids[@]}"
kill $sampler
echo "wave done"
