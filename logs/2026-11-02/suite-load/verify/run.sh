#!/usr/bin/env bash
# The check after the second review, on the final suite commit: one full CI run from a clean build,
# two copies of rounds.sh (8 rounds each) at once, and the load average every 15 s.
# Run from the worktree's root: bash logs/2026-11-02/suite-load/verify/run.sh
here=logs/2026-11-02/suite-load/verify
host=$(head -n 1 .build-host)
git rev-parse --short HEAD > "$here/commit"
ssh "$host" 'while :; do echo "$(date --utc +%FT%TZ) $(cat /proc/loadavg)"; sleep 15; done' > "$here/loadavg.txt" &
sampler=$!
( mkdir --parents "$here/ci"
  CTR_EXTRA='--sysctl net.ipv4.tcp_syn_retries=2' LEAN_HTTP_REMOTE_DIR=lean-http-load-1 \
    scripts/remote.sh bash -c 'rm -rf .lake out && lean --version && bash scripts/ci.sh' > "$here/ci/console.txt" 2>&1
  rsync --archive --exclude tls-certs "$host:lean-http-load-1/out/ci" "$host:lean-http-load-1/out/net" "$here/ci/" ) &
p1=$!
for k in 4 5; do
  ( CTR_EXTRA='--sysctl net.ipv4.tcp_syn_retries=2' LEAN_HTTP_REMOTE_DIR=lean-http-load-$k \
      scripts/remote.sh bash -c "$(cat logs/2026-11-02/suite-load/rounds.sh)" rounds.sh 8 > "$here/rounds-$k.txt" 2>&1 ) &
done
wait
kill $sampler
echo "verify done"
