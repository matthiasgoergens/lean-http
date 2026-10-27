#!/usr/bin/env bash
# Real-socket tests of the client over loopback, against the local servers in this directory.
#
# Runs inside the container that scripts/remote.sh starts (no network but its own loopback, uv's
# CPython at /py), after `lake build net-client`.  From the repository root:
#
#   CTR_EXTRA='--sysctl net.ipv4.tcp_syn_retries=2' scripts/remote.sh bash tests/net/run.sh [name...]
#
# The sysctl makes the kernel give up on an unanswered SYN after about 7 s instead of about 127 s,
# so that the descriptor check of the blackhole scenario finishes quickly.
#
# Writes one file per scenario to out/net/<name>.txt, each starting with the client's command and
# ending with its exit status, wall time and how long the process took to exit after `main`
# returned, plus the logs of the servers it used; prints PASS or FAIL per check and a summary.

PY=${PY:-/py/bin/python3}
BIN=/w/.lake/build/bin/net-client
here=/w/tests/net
out=/w/out/net
mkdir --parents "$out" || exit 1

pids=()
cleanup() {
  for p in "${pids[@]}"; do kill "$p" 2>/dev/null; done
  for p in "${pids[@]}"; do wait "$p" 2>/dev/null; done
  pids=()
}
trap cleanup EXIT

passes=0
fails=0
knowns=0
result() { # result <PASS|FAIL|KNOWN> <scenario> <description>
  echo "$1 $2: $3" | tee --append "$out/summary.txt"
  case $1 in
    PASS) passes=$((passes + 1)) ;;
    KNOWN) knowns=$((knowns + 1)) ;;
    *) fails=$((fails + 1)) ;;
  esac
}

# start <scenario> <server name> <ready text> <command...>: start a server, wait for <ready text>.
start() {
  local scenario=$1 name=$2 ready=$3; shift 3
  local log="$out/$scenario.$name.log"
  "$@" > "$log" 2>&1 &
  pids+=($!)
  for _ in $(seq 100); do
    grep --quiet --fixed-strings "$ready" "$log" 2>/dev/null && return 0
    sleep 0.05
  done
  echo "server $name for $scenario did not become ready" >&2
  cat "$log" >&2
  return 1
}

# client <scenario> <net-client args...>: run the client once, record its output and timings.
# A non-zero exit status or a slow exit is a FAIL, or KNOWN with the reason in $known_exit.
client() {
  local scenario=$1; shift
  local file="$out/$scenario.txt"
  echo "\$ net-client $*" > "$file"
  local t0 t1 rc
  t0=$(date +%s%N)
  timeout 60 "$BIN" "$@" >> "$file" 2>&1
  rc=$?
  t1=$(date +%s%N)
  local wall=$(( (t1 - t0) / 1000000 ))
  local main
  main=$(sed --quiet 's/^main returning at ms=\([0-9]*\)\..*/\1/p' "$file")
  local after=$(( wall - ${main:-$wall} ))
  echo "exit status=$rc wall_ms=$wall exit_after_main_ms=$after" >> "$file"
  if [ -z "$main" ]; then
    result FAIL "$scenario" "main never returned (status $rc)"
  elif { [ "$after" -gt 1000 ] || [ "$rc" -ne 0 ]; } && [ -n "${known_exit:-}" ]; then
    result KNOWN "$scenario" "exit status $rc, ${after} ms after main returned: $known_exit"
  elif [ "$rc" -ne 0 ]; then
    result FAIL "$scenario" "exit status $rc, ${after} ms after main returned"
  elif [ "$after" -gt 1000 ]; then
    result FAIL "$scenario" "process took ${after} ms to exit after main returned"
  else
    result PASS "$scenario" "process exited ${after} ms after main returned"
  fi
}

# expect <scenario> <extended regex> <description>: check the client's output.
expect() {
  if grep --quiet --extended-regexp "$2" "$out/$1.txt"; then
    result PASS "$1" "$3"
  else
    result FAIL "$1" "$3 (no match for: $2)"
  fi
}

# call_ms <scenario>: the time of the first call, in whole milliseconds.
call_ms() {
  sed --quiet 's/^call 0 .* ms=\([0-9]*\)\..*/\1/p' "$out/$1.txt" | head --lines=1
}

# within <scenario> <lo> <hi> <description>: the first call took between lo and hi ms.
within() {
  local ms
  ms=$(call_ms "$1")
  if [ -n "$ms" ] && [ "$ms" -ge "$2" ] && [ "$ms" -le "$3" ]; then
    result PASS "$1" "$4: ${ms} ms"
  else
    result FAIL "$1" "$4: ${ms:-no} ms, expected ${2}-${3}"
  fi
}

# median_within <scenario> <lo> <hi> <description>: the median of repeated calls is in [lo, hi] ms.
median_within() {
  local ms
  ms=$(sed --quiet 's/^summary .* p50=\([0-9]*\)\..*/\1/p' "$out/$1.txt")
  if [ -n "$ms" ] && [ "$ms" -ge "$2" ] && [ "$ms" -le "$3" ]; then
    result PASS "$1" "$4: ${ms} ms"
  else
    result FAIL "$1" "$4: ${ms:-no} ms, expected ${2}-${3}"
  fi
}

EVIL=18080      # evil.py on 127.0.0.1
EVIL6=18081     # evil.py on ::1
ONEWRITE=18082  # onewrite.py on 127.0.0.1
DUAL=18083      # blackhole on ::1, evil.py on 127.0.0.1
HOLE=18084      # blackhole on ::1 only
CLOSED=18085    # nothing listens
HOLE2=18086     # blackhole on ::1 only, for the connect deadline
NOREAD=18087    # accepts and never reads
LARGE=18088     # onewrite.py, for a large POST

# Names for the resolver tests.  getaddrinfo without a socket type returns each of these addresses
# once per socket type, three times in all.
grep --quiet 'dual\.test' /etc/hosts || {
  printf '127.0.0.1 dup.test\n::1 dual.test\n127.0.0.1 dual.test\n' >> /etc/hosts || exit 1
}

servers() {
  start shared evil "listening" "$PY" -I "$here/evil.py" --port $EVIL || return 1
}

scenario() { # scenario <name>: true if the scenario was asked for (or none were)
  [ ${#selected[@]} -eq 0 ] && return 0
  local s; for s in "${selected[@]}"; do [ "$s" = "$1" ] && { matched+=("$1"); return 0; }; done
  return 1
}
matched=()
selected=("$@")
rm --force "$out"/*.txt "$out"/*.log
echo "### $(date --utc +%FT%TZ) $(uname -r); syn_retries=$(cat /proc/sys/net/ipv4/tcp_syn_retries)" \
  | tee "$out/summary.txt"

servers || exit 1

if scenario get; then
  client get call GET "http://127.0.0.1:$EVIL/ok"
  expect get 'call 0 ok status=200 bytes=5 .*address=127\.0\.0\.1:18080' "GET returns the body"
fi

if scenario post; then
  client post call POST "http://127.0.0.1:$EVIL/echo" body=11
  expect post 'call 0 ok status=200 .*body_start="POST /echo ' "POST is answered"
  if grep --quiet --extended-regexp "POST /echo \{'host': \['127\.0\.0\.1:18080'\], 'connection': \['close'\], 'content-length': \['11'\]\} body=11B" "$out/shared.evil.log"; then
    result PASS post "the server read Host, Content-Length: 11, Connection: close and an 11-byte body"
  else
    result FAIL post "the server did not log an 11-byte body"
  fi
fi

if scenario head; then
  client head call HEAD "http://127.0.0.1:$EVIL/head-cl"
  expect head 'call 0 ok status=200 bytes=0 ' "HEAD with Content-Length: 12345 has an empty body"
fi

if scenario chunked; then
  client chunked call GET "http://127.0.0.1:$EVIL/chunked-ext"
  expect chunked 'call 0 ok status=200 bytes=11 .*body_start="hello world"' \
    "chunked body with extensions and trailers"
fi

if scenario interim; then
  client interim call GET "http://127.0.0.1:$EVIL/early-hints"
  expect interim 'call 0 ok status=200 bytes=8 .*body_start="after103"' "two 103 responses, then 200"
fi

if scenario ipv6-literal; then
  start ipv6-literal evil6 "listening" "$PY" -I "$here/evil.py" --port $EVIL6 --v6 --host ::1 || exit 1
  client ipv6-literal call GET "http://[::1]:$EVIL6/ok"
  expect ipv6-literal 'call 0 ok status=200 bytes=5 .*address=\[::1\]:18081' "an IPv6 literal URL connects"
fi

if scenario dns-dup; then
  getent ahosts dup.test > "$out/dns-dup.getent.log" 2>&1
  getent ahosts dual.test > "$out/dns-dual.getent.log" 2>&1
  client dns-dup call GET "http://dup.test:$CLOSED/" retries=0
  expect dns-dup 'attempts=\[127\.0\.0\.1:18085#0:failed\([^]]*\)\]$' \
    "a name with one address (returned three times) gets one attempt"
fi

if scenario dns-dual; then
  client dns-dual call GET "http://dual.test:$CLOSED/" retries=0
  refused='failed\(no such thing \(error code: 111, connection refused\)\)'
  expect dns-dual "attempts=\\[\\[::1\\]:18085#0:$refused, 127\\.0\\.0\\.1:18085#0:$refused\\]\$" \
    "a name with two addresses (each returned three times) gets two attempts, ::1 first"
fi

if scenario blackhole-first; then
  start blackhole-first hole "blackhole" "$PY" -I "$here/blackhole.py" ::1 $DUAL || exit 1
  start blackhole-first evil "listening" "$PY" -I "$here/evil.py" --port $DUAL || exit 1
  client blackhole-first call GET "http://dual.test:$DUAL/ok" repeat=10
  expect blackhole-first 'call 0 ok status=200 bytes=5 .*address=127\.0\.0\.1:18083' \
    "connects to 127.0.0.1 when ::1 drops SYNs"
  expect blackhole-first 'summary calls n=10 .* ok=10$' "ten calls out of ten"
  expect blackhole-first 'failed_attempts=\[\[::1\]:18083#0:abandoned\]' "the ::1 attempt was abandoned"
  # Each call's connection must close before the next call connects.  A connection kept open by the
  # abandoned ::1 attempt would close only when the kernel gives up on that attempt, or at exit.
  ordered=1
  for k in $(seq 1 9); do
    eof=$(grep --line-number "conn$k EOF from client" "$out/blackhole-first.evil.log" | cut --delimiter=: --fields=1 | head --lines=1)
    next=$(grep --line-number "conn$((k + 1)) accepted" "$out/blackhole-first.evil.log" | cut --delimiter=: --fields=1 | head --lines=1)
    { [ -n "$eof" ] && [ -n "$next" ] && [ "$eof" -lt "$next" ]; } || ordered=0
  done
  if [ $ordered -eq 1 ]; then
    result PASS blackhole-first "each call's connection closed before the next call connected"
  else
    result FAIL blackhole-first "a call's connection was still open when the next call connected"
  fi
  median_within blackhole-first 240 400 "median call within about the 250 ms stagger"
  client blackhole-stagger50 call GET "http://dual.test:$DUAL/ok" repeat=10 stagger=50
  median_within blackhole-stagger50 40 200 "with a 50 ms stagger, the median call is about 50 ms"
fi

if scenario blackhole-timeout; then
  start blackhole-timeout hole "blackhole" "$PY" -I "$here/blackhole.py" ::1 $HOLE || exit 1
  client blackhole-timeout call GET "http://[::1]:$HOLE/" connect=1000 retries=1 seed=1 linger=9000
  expect blackhole-timeout 'call 0 error delivery=not sent .*attempts=\[\[::1\]:18084#0:timedOut, \[::1\]:18084#1:timedOut\]' \
    "two connect attempts time out; nothing sent"
  within blackhole-timeout 2000 2400 "two 1 s attempts and one backoff"
  calls=$(sed --quiet 's/^fds_after_calls=//p' "$out/blackhole-timeout.txt")
  later=$(sed --quiet 's/^fds_after_linger_9000ms=//p' "$out/blackhole-timeout.txt")
  if [ -n "$calls" ] && [ -n "$later" ] && [ "$later" -le $((calls - 2)) ]; then
    result PASS blackhole-timeout "the abandoned attempts' sockets are released later ($calls, then $later descriptors)"
  else
    result FAIL blackhole-timeout "descriptors after the call: ${calls:-?}, 9 s later: ${later:-?}"
  fi
fi

if scenario refused-backoff; then
  "$BIN" backoff 42 > "$out/refused-backoff.schedule.txt" 2>&1
  client refused-backoff call GET "http://127.0.0.1:$CLOSED/" seed=42
  expect refused-backoff 'call 0 error delivery=not sent .*rounds=3 seed=42 .*could not connect' \
    "refused three times (two retries); nothing sent"
  expect refused-backoff 'attempts=\[127\.0\.0\.1:18085#0:failed\([^]]*\), 127\.0\.0\.1:18085#1:failed\([^]]*\), 127\.0\.0\.1:18085#2:failed\([^]]*\)\]' \
    "one attempt per round"
  # backoff 42 gives [23, 49]: the call takes at least their sum.
  within refused-backoff 72 400 "at least the 23 + 49 ms of backoff for seed 42"
fi

if scenario deadline-trickle; then
  client deadline-trickle call GET "http://127.0.0.1:$EVIL/trickle?ms=100" deadline=2000 gap=1000
  expect deadline-trickle 'call 0 error delivery=response received .*status=\(some 200\) cause="deadline timeout"' \
    "a body trickling one byte per 100 ms ends at the deadline"
  within deadline-trickle 1990 2400 "at the 2 s deadline"
fi

if scenario deadline-interim; then
  client deadline-interim call GET "http://127.0.0.1:$EVIL/interim-forever?ms=300" deadline=2000
  expect deadline-interim 'call 0 error delivery=maybe delivered .*cause="deadline timeout"' \
    "interim responses every 300 ms, never a final one, end at the deadline"
  within deadline-interim 1990 2400 "at the 2 s deadline"
fi

if scenario interim-limit; then
  client interim-limit call GET "http://127.0.0.1:$EVIL/interim-forever?ms=5"
  expect interim-limit 'call 0 error delivery=maybe delivered .*cause="interim responses limit exceeded"' \
    "the eleventh interim response fails the call"
fi

if scenario read-gap; then
  client read-gap call GET "http://127.0.0.1:$EVIL/stall-head?ms=3000" gap=1000
  expect read-gap 'call 0 error delivery=maybe delivered .*cause="read timeout"' "a silent server hits the read gap"
  within read-gap 990 1400 "after the 1 s gap"
fi

if scenario body-limit; then
  client body-limit call GET "http://127.0.0.1:$EVIL/bigbody?n=10000000" maxbody=1000000
  expect body-limit 'call 0 error delivery=response received .*cause="body size limit exceeded"' \
    "a 10 MB body against a 1 MB limit"
fi

if scenario malformed; then
  client malformed call GET "http://127.0.0.1:$EVIL/badstatus"
  expect malformed 'call 0 error delivery=maybe delivered .*cause="invalid response: Bad message"' \
    "a malformed status line"
fi

if scenario cut-body; then
  client cut-body call GET "http://127.0.0.1:$EVIL/cl-mismatch"
  expect cut-body 'call 0 error delivery=response received .*cause="the connection closed before a complete response"' \
    "the server closes 95 bytes short of its Content-Length"
fi

if scenario reset; then
  client reset call GET "http://127.0.0.1:$EVIL/rst"
  expect reset 'call 0 error delivery=maybe delivered .*cause="the connection closed before a complete response"' \
    "the server resets the connection instead of answering"
fi

if scenario resolve; then
  client resolve call GET "http://nonexistent.invalid/"
  expect resolve 'call 0 error delivery=not sent .*could not resolve nonexistent\.invalid' \
    "a name that does not resolve; not retried"
fi

if scenario nodelay; then
  start nodelay onewrite "listening" "$PY" -I "$here/onewrite.py" --port $ONEWRITE --log "$out/nodelay.recv.log" || exit 1
  client nodelay call POST "http://127.0.0.1:$ONEWRITE/" body=100 repeat=300
  client nodelay-off call POST "http://127.0.0.1:$ONEWRITE/" body=100 repeat=300 nodelay=0
  client nodelay-raw-split-keepalive rawpost $ONEWRITE n=50 size=100 keepalive=1 nodelay=0
  client nodelay-raw-split-keepalive-nodelay rawpost $ONEWRITE n=300 size=100 keepalive=1 nodelay=1
  client nodelay-raw-split-fresh rawpost $ONEWRITE n=300 size=100 keepalive=0 nodelay=0
  p50() { sed --quiet 's/^summary .* p50=\([0-9]*\)\..*/\1/p' "$out/$1.txt"; }
  for s in nodelay nodelay-off nodelay-raw-split-fresh nodelay-raw-split-keepalive-nodelay; do
    v=$(p50 $s)
    if [ -n "$v" ] && [ "$v" -lt 20 ]; then
      result PASS $s "median call ${v} ms, no 40 ms stall"
    else
      result FAIL $s "median call ${v:-?} ms"
    fi
  done
  v=$(p50 nodelay-raw-split-keepalive)
  if [ -n "$v" ] && [ "$v" -ge 20 ]; then
    result PASS nodelay-raw-split-keepalive "control: split writes with Nagle on a kept-alive connection stall (median ${v} ms)"
  else
    result FAIL nodelay-raw-split-keepalive "control did not stall (median ${v:-?} ms): the harness cannot see the effect"
  fi
fi

if scenario post-large; then
  start post-large onewrite "listening" "$PY" -I "$here/onewrite.py" --port $LARGE || exit 1
  client post-large call POST "http://127.0.0.1:$LARGE/" body=3000000
  expect post-large 'call 0 ok status=200 bytes=12 ' "a 3 MB body goes out in slices and is answered"
fi

if scenario connect-deadline; then
  start connect-deadline hole "blackhole" "$PY" -I "$here/blackhole.py" ::1 $HOLE2 || exit 1
  client connect-deadline call GET "http://[::1]:$HOLE2/" deadline=1500
  expect connect-deadline 'call 0 error delivery=not sent .*cause="deadline timeout"' \
    "the deadline passes while connecting; nothing sent"
  within connect-deadline 1490 1900 "at the 1.5 s deadline"
fi

if scenario write-timeout; then
  start write-timeout noread "listening" "$PY" -I "$here/noread.py" $NOREAD || exit 1
  client write-timeout call POST "http://127.0.0.1:$NOREAD/" body=32000000 gap=1000
  expect write-timeout 'call 0 error delivery=maybe delivered .*cause="write timeout" detail="[0-9]+ of 32000[0-9]+ request bytes accepted"' \
    "a peer that stops reading stalls the upload; the write gap ends it"
fi

# Last, because it points the resolver at a name server that never answers.
if scenario dns-timeout; then
  cp /etc/resolv.conf /tmp/resolv.conf.saved 2>/dev/null || : > /tmp/resolv.conf.saved
  printf 'nameserver 127.0.0.1\n' > /etc/resolv.conf || exit 1
  start dns-timeout dns "listening" "$PY" -I "$here/dnsblack.py" || exit 1
  known_exit="the abandoned lookup delays exit until the resolver gives up, and the process often crashes then (NOTES.md)" \
    client dns-timeout call GET "http://slow.test/" deadline=2000
  cp /tmp/resolv.conf.saved /etc/resolv.conf
  expect dns-timeout 'call 0 error delivery=not sent .*cause="deadline timeout"' \
    "a name server that never answers: the call ends at the deadline; nothing sent"
  within dns-timeout 1990 2400 "at the 2 s deadline"
fi

cleanup
# A name that matches no scenario, or a run with no checks at all, must not pass silently.
for s in "${selected[@]}"; do
  case " ${matched[*]} " in *" $s "*) ;; *) echo "FAIL $s: no such scenario" | tee --append "$out/summary.txt"; fails=$((fails + 1)) ;; esac
done
if [ $((passes + fails + knowns)) -eq 0 ]; then
  echo "FAIL run: no checks ran" | tee --append "$out/summary.txt"; fails=1
fi
echo "### $passes passed, $fails failed, $knowns known limitations" | tee --append "$out/summary.txt"
[ "$fails" -eq 0 ]
