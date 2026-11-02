# Repeats the scenarios whose checks of time changed ROUNDS times in the build container, printing
# each round's load average and verdicts and keeping the outputs of any round with a failure under
# out/rounds/<n>/.  Run from the laptop (logs/ is not copied over), as
#   CTR_EXTRA='--sysctl net.ipv4.tcp_syn_retries=2' LEAN_HTTP_REMOTE_DIR=<dir> \
#     scripts/remote.sh bash -c "$(cat logs/2026-11-02/suite-load/rounds.sh)" rounds.sh ROUNDS
rounds=${1:-10}
scenarios="blackhole-first refused-backoff blackhole-timeout deadline-trickle deadline-interim read-gap connect-deadline
  early-response keepalive-close idle-408 concurrency redispatch-refused redispatch-408 retry-after
  stream-abandon upload-early upload-redispatch upload-exit tls-handshake tls-idle tls-stream timers
  cancel-head cancel-body cancel-tls cancel-cap shutdown dns-timeout"
lake build net-client 2>&1 | tail --lines=1
mkdir --parents out && rm --recursive --force out/rounds
for i in $(seq "$rounds"); do
  echo "=== round $i $(date --utc +%FT%TZ) loadavg $(cat /proc/loadavg)"
  # shellcheck disable=SC2086
  bash tests/net/run.sh $scenarios > out/round.txt 2>&1
  grep --extended-regexp '^(FAIL|KNOWN|SKIP|###)' out/round.txt | cut --characters=1-300
  if grep --quiet '^FAIL' out/round.txt; then
    mkdir --parents "out/rounds/$i" && cp out/round.txt out/net/*.txt out/net/*.log "out/rounds/$i/"
  fi
done
echo "=== done $(date --utc +%FT%TZ) loadavg $(cat /proc/loadavg)"
