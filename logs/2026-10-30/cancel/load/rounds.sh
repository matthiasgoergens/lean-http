# Repeats the cancellation and shutdown scenarios, and the stream-race ones, ROUNDS times in the
# build container, printing each round's load average and verdicts and keeping the outputs of any
# round with a failure under out/rounds/<n>/.  Run from the laptop (logs/ is not copied over), as
#   CTR_EXTRA='--sysctl net.ipv4.tcp_syn_retries=2' LEAN_HTTP_REMOTE_DIR=<dir> \
#     scripts/remote.sh bash -c "$(cat logs/2026-10-30/cancel/load/rounds.sh)" rounds.sh ROUNDS
rounds=${1:-20}
scenarios="cancel-before cancel-head cancel-body cancel-upload cancel-tls cancel-backoff cancel-connect
  cancel-cap shutdown cancel-steps stream-abandon tls-stream dns-timeout"
lake build net-client 2>&1 | tail --lines=1
mkdir --parents out && rm --recursive --force out/rounds
for i in $(seq "$rounds"); do
  echo "=== round $i $(date --utc +%FT%TZ) loadavg $(cat /proc/loadavg)"
  # shellcheck disable=SC2086
  bash tests/net/run.sh $scenarios > out/round.txt 2>&1
  grep --extended-regexp '^(FAIL|KNOWN|###)' out/round.txt | cut --characters=1-300
  if grep --quiet '^FAIL' out/round.txt; then
    mkdir --parents "out/rounds/$i" && cp out/round.txt out/net/*.txt out/net/*.log "out/rounds/$i/"
  fi
done
echo "=== done $(date --utc +%FT%TZ) loadavg $(cat /proc/loadavg)"
