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
# It also runs outside that container (scripts/ci.sh, on a CI runner), with $PY or python3.  What
# the environment cannot support is skipped, with a SKIP line saying why: the scenarios that need
# the names of tests/net/hosts when /etc/hosts lacks them and cannot be written, those that need
# IPv6 loopback when ::1 is not usable, the descriptor check of blackhole-timeout when
# tcp_syn_retries is above 2, and dns-timeout when not run as root (it rewrites /etc/resolv.conf and
# listens on port 53).
#
# Writes one file per scenario to out/net/<name>.txt, each starting with the client's command and
# ending with its exit status, wall time and how long the process took to exit after `main`
# returned, plus the logs of the servers it used; prints PASS, FAIL, KNOWN or SKIP per check and a
# summary.

root=$(cd "$(dirname "$0")/../.." && pwd) || exit 1
if [ -z "${PY:-}" ]; then
  if [ -x /py/bin/python3 ]; then PY=/py/bin/python3; else PY=python3; fi
fi
BIN=$root/.lake/build/bin/net-client
here=$root/tests/net
out=$root/out/net
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
skips=0
result() { # result <PASS|FAIL|KNOWN|SKIP> <scenario> <description>
  echo "$1 $2: $3" | tee --append "$out/summary.txt"
  case $1 in
    PASS) passes=$((passes + 1)) ;;
    KNOWN) knowns=$((knowns + 1)) ;;
    SKIP) skips=$((skips + 1)) ;;
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
  sed --quiet 's/^\(stream \)\{0,1\}\(call\|stream\) 0 .* ms=\([0-9]*\)\..*/\3/p' "$out/$1.txt" | head --lines=1
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
  # The summary of all calls (net-client also summarises the later calls and the idle checks).
  ms=$(sed --quiet '/^summary \(later calls\|idle checks\) /d; s/^summary .* p50=\([0-9]*\)\..*/\1/p' "$out/$1.txt")
  if [ -n "$ms" ] && [ "$ms" -ge "$2" ] && [ "$ms" -le "$3" ]; then
    result PASS "$1" "$4: ${ms} ms"
  else
    result FAIL "$1" "$4: ${ms:-no} ms, expected ${2}-${3}"
  fi
}

# trace_ok <scenario>: net-client replayed every call's steps through the planner (`Call.validate`).
trace_ok() {
  if grep --quiet 'trace call .* FAIL' "$out/$1.txt"; then
    result FAIL "$1" "the client did something the planner did not say: $(grep --max-count=1 'trace call .* FAIL' "$out/$1.txt")"
  elif grep --quiet 'trace call .* ok' "$out/$1.txt"; then
    result PASS "$1" "every call's steps replay through the planner"
  else
    result FAIL "$1" "no call's steps were checked"
  fi
}

# gaps_within <scenario> <slack>: every retry went out no earlier than its delay and at most <slack>
# ms after it, from the time the planner decided.  Never early is the property; the slack only allows
# for a loaded machine (30 ms failed under load: a timer woke up to 100 ms late).
gaps_within() {
  local line delays gaps ok=1 i
  line=$(grep --max-count=1 '^trace call 0 retry delays=' "$out/$1.txt")
  delays=($(echo "$line" | sed 's/.*delays=\[\([^]]*\)\].*/\1/' | tr ',' ' '))
  gaps=($(echo "$line" | sed 's/.*gaps=\[\([^]]*\)\].*/\1/' | tr ',' ' '))
  [ ${#delays[@]} -gt 0 ] && [ ${#delays[@]} -eq ${#gaps[@]} ] || ok=0
  for i in "${!delays[@]}"; do
    [ "${gaps[$i]}" -ge "${delays[$i]}" ] && [ "${gaps[$i]}" -le $(( ${delays[$i]} + $2 )) ] || ok=0
  done
  if [ $ok -eq 1 ]; then
    result PASS "$1" "each retry waited its delay, at most $2 ms more (delays ${delays[*]}, gaps ${gaps[*]})"
  else
    result FAIL "$1" "retry gaps outside [delay, delay + $2]: ${line:-no retries recorded}"
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
EARLY=18089     # early.py: answers 413 after the head, then reads no more
# 18090-18101 and 18104: the pooling scenarios, each with an evil.py of its own; 18102: idle.py
# 18110-18120: the planner's and the streaming scenarios; 18130-18173: the TLS scenarios

# Scenarios the environment cannot run, with the reason.
declare -A unavailable=()

# Names for the resolver tests (tests/net/hosts).  getaddrinfo without a socket type returns each of
# these addresses once per socket type, three times in all.
if ! grep --quiet 'dual\.test' /etc/hosts || ! grep --quiet 'wild\.lh\.test' /etc/hosts; then
  if [ -w /etc/hosts ]; then
    cat "$here/hosts" >> /etc/hosts || exit 1
  else
    for s in dns-dup dns-dual blackhole-first tls-names; do
      unavailable[$s]="/etc/hosts lacks the names of tests/net/hosts and cannot be written"
    done
  fi
fi
if ! "$PY" -I -c 'import socket; s = socket.socket(socket.AF_INET6); s.bind(("::1", 0))' 2>/dev/null; then
  for s in ipv6-literal dns-dual blackhole-first blackhole-timeout connect-deadline; do
    unavailable[$s]="IPv6 loopback (::1) is not usable"
  done
fi
if [ "$(id --user)" -ne 0 ]; then
  unavailable[dns-timeout]="needs root, to rewrite /etc/resolv.conf and listen on port 53"
fi
syn_retries=$(cat /proc/sys/net/ipv4/tcp_syn_retries)
# The TLS scenarios need the openssl command-line tool to make their certificates.
certs=$out/tls-certs
if ! command -v openssl > /dev/null; then
  for s in tls-get tls-reuse tls-verify tls-trust tls-close tls-stray tls-redirect tls-handshake tls-idle \
      tls-latched tls-12 tls-names tls-stream; do
    unavailable[$s]="the openssl command-line tool, which makes the test certificates, is not installed"
  done
elif ! { mkdir --parents "$certs" && bash "$here/tls-certs.sh" "$certs" > "$certs/made.out" 2>&1; }; then
  echo "tests/net/tls-certs.sh failed:" >&2
  cat "$certs/made.out" >&2
  exit 1
fi

servers() {
  start shared evil "listening" "$PY" -I "$here/evil.py" --port $EVIL || return 1
}

scenario() { # scenario <name>: true if the scenario was asked for (or none were) and can run here
  local s asked=0
  if [ ${#selected[@]} -eq 0 ]; then
    asked=1
  else
    for s in "${selected[@]}"; do [ "$s" = "$1" ] && { matched+=("$1"); asked=1; }; done
  fi
  [ $asked -eq 1 ] || return 1
  if [ -n "${unavailable[$1]:-}" ]; then
    result SKIP "$1" "${unavailable[$1]}"
    return 1
  fi
  return 0
}
matched=()
selected=("$@")
rm --force "$out"/*.txt "$out"/*.log
echo "### $(date --utc +%FT%TZ) $(uname -r); syn_retries=$syn_retries; uid=$(id --user)" \
  | tee "$out/summary.txt"

servers || exit 1

if scenario get; then
  client get call GET "http://127.0.0.1:$EVIL/ok"
  expect get 'call 0 ok status=200 bytes=5 .*address=127\.0\.0\.1:18080' "GET returns the body"
fi

if scenario post; then
  client post call POST "http://127.0.0.1:$EVIL/echo" body=11
  expect post 'call 0 ok status=200 .*body_start="POST /echo ' "POST is answered"
  if grep --quiet --extended-regexp "POST /echo \{'host': \['127\.0\.0\.1:18080'\], 'connection': \['keep-alive'\], 'content-length': \['11'\]\} body=11B" "$out/shared.evil.log"; then
    result PASS post "the server read Host, Content-Length: 11, Connection: keep-alive and an 11-byte body"
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
  # Without pooling, so that every call connects (and the ::1 attempt is abandoned every time).
  client blackhole-first call GET "http://dual.test:$DUAL/ok" repeat=10 pool=0
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
  client blackhole-stagger50 call GET "http://dual.test:$DUAL/ok" repeat=10 stagger=50 pool=0
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
  if [ "$syn_retries" -gt 2 ]; then
    result SKIP blackhole-timeout "the release of the abandoned attempts' sockets: with tcp_syn_retries=$syn_retries the kernel gives up on a SYN after the 9 s this waits"
  elif [ -n "$calls" ] && [ -n "$later" ] && [ "$later" -le $((calls - 2)) ]; then
    result PASS blackhole-timeout "the abandoned attempts' sockets are released later ($calls, then $later descriptors)"
  else
    result FAIL blackhole-timeout "descriptors after the call: ${calls:-?}, 9 s later: ${later:-?}"
  fi
fi

if scenario refused-backoff; then
  "$BIN" backoff 42 > "$out/refused-backoff.schedule.txt" 2>&1
  client refused-backoff call GET "http://127.0.0.1:$CLOSED/" seed=42
  expect refused-backoff 'call 0 error delivery=not sent .*rounds=3 seed=42 .*retries=2 not_retried=LeanHttp.Call.NoRetry.hopLimit .*could not connect' \
    "refused three times (two retries by the planner); nothing sent"
  expect refused-backoff 'attempts=\[127\.0\.0\.1:18085#0:failed\([^]]*\), 127\.0\.0\.1:18085#1:failed\([^]]*\), 127\.0\.0\.1:18085#2:failed\([^]]*\)\]' \
    "one connect round per attempt"
  # backoff 42 gives [23, 49]: the call takes at least their sum.
  within refused-backoff 72 400 "at least the 23 + 49 ms of backoff for seed 42"
  expect refused-backoff '^trace call 0 retry delays=\[23, 49\] ' "the planner's delays are the schedule of seed 42"
  gaps_within refused-backoff 150
  trace_ok refused-backoff
  # With a backoff of up to 1 s and a deadline of 300 ms: seed 5 draws 738 ms for the first retry,
  # which would reach the deadline, so the call fails at once rather than wait for it.
  "$BIN" backoff 5 base=1000 cap=1000 n=1 > "$out/refused-deadline.schedule.txt" 2>&1
  client refused-deadline call GET "http://127.0.0.1:$CLOSED/" seed=5 base=1000 cap=1000 deadline=300
  expect refused-deadline 'call 0 error delivery=not sent .*rounds=1 .*retries=0 not_retried=LeanHttp.Call.NoRetry.noTime .*could not connect' \
    "a retry whose backoff would reach the deadline is not made"
  within refused-deadline 0 100 "the call fails at once, not at the deadline"
  trace_ok refused-deadline
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
  client read-gap call GET "http://127.0.0.1:$EVIL/stall-head?ms=3000" gap=1000 retries=0
  expect read-gap 'call 0 error delivery=maybe delivered .*cause="read timeout"' "a silent server hits the read gap"
  within read-gap 990 1400 "after the 1 s gap"
  # A GET can be sent again after a read timeout: twice more, after backoffs of at most 100 and
  # 200 ms.
  client read-gap-retried call GET "http://127.0.0.1:$EVIL/stall-head?ms=3000" gap=1000
  expect read-gap-retried 'call 0 error delivery=maybe delivered .*retries=2 not_retried=LeanHttp.Call.NoRetry.hopLimit .*cause="read timeout"' \
    "by default the GET is tried three times"
  within read-gap-retried 2990 3700 "three 1 s gaps and two backoffs"
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
  p50() { sed --quiet '/^summary \(later calls\|idle checks\) /d; s/^summary .* p50=\([0-9]*\)\..*/\1/p' "$out/$1.txt"; }
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

if scenario early-response; then
  start early-response early "listening" "$PY" -I "$here/early.py" $EARLY || exit 1
  client early-response call POST "http://127.0.0.1:$EARLY/" body=32000000 gap=1000
  expect early-response 'call 0 ok status=413 bytes=3 .*body_start="big"' \
    "a server that answers 413 after the head and stops reading: the response is delivered"
  within early-response 0 900 "before the 1 s write gap"
fi

# --- Pooling.  Each scenario has an evil.py of its own, so that its log counts the connections.

# conns <scenario> <n> <description>: the scenario's server accepted exactly n connections.
conns() {
  local got
  got=$(grep --count ' accepted from ' "$out/$1.evil.log")
  if [ "$got" -eq "$2" ]; then
    result PASS "$1" "$3: $got"
  else
    result FAIL "$1" "$3: $got, expected $2"
  fi
}

# logged <scenario> <extended regex> <description>: the scenario's server logged a match.
logged() {
  if grep --quiet --extended-regexp "$2" "$out/$1.evil.log"; then
    result PASS "$1" "$3"
  else
    result FAIL "$1" "$3 (no match in the server log for: $2)"
  fi
}

evil() { # evil <scenario> <port>: an evil.py for one scenario
  start "$1" evil "listening" "$PY" -I "$here/evil.py" --port "$2"
}

if scenario pool-reuse; then
  evil pool-reuse 18090 || exit 1
  client pool-reuse call GET "http://127.0.0.1:18090/ok" repeat=3
  expect pool-reuse 'call 0 ok status=200 .* conn=\(some 0\) reused=false' "the first call opens connection 0"
  expect pool-reuse 'call 1 ok status=200 .* conn=\(some 0\) reused=true discarded=0 .*redispatched=false' \
    "the second call reuses it after a clean idle check"
  expect pool-reuse 'call 2 ok status=200 .* conn=\(some 0\) reused=true discarded=0 ' "so does the third"
  expect pool-reuse '^pool idle=1 checked_out=0 allocated=1$' "one idle connection at the end"
  conns pool-reuse 1 "the server saw one connection for three calls"
  logged pool-reuse "req3 GET /ok \{'host': \['127\.0\.0\.1:18090'\], 'connection': \['keep-alive'\]\}" \
    "the requests say Connection: keep-alive"
fi

if scenario pool-off; then
  evil pool-off 18091 || exit 1
  client pool-off call GET "http://127.0.0.1:18091/ok" repeat=3 pool=0
  expect pool-off 'call 2 ok status=200 .* conn=none reused=false' "with pooling off, no call reuses"
  conns pool-off 3 "the server saw a connection per call"
  logged pool-off "req1 GET /ok \{'host': \['127\.0\.0\.1:18091'\], 'connection': \['close'\]\}" \
    "the requests say Connection: close"
fi

if scenario keepalive-close; then
  # The server closes a connection 200 ms after its last response; the next call comes 500 ms later.
  evil keepalive-close 18092 || exit 1
  client keepalive-close call GET "http://127.0.0.1:18092/close-after-idle?ms=200" repeat=3 pause=500
  expect keepalive-close 'call 1 ok status=200 .*reused=false discarded=1 .*redispatched=false' \
    "the idle check finds the closed connection; the call opens a new one"
  expect keepalive-close 'call 2 ok status=200 .*reused=false discarded=1 .*redispatched=false' "and again"
  expect keepalive-close 'summary calls n=3 .* ok=3$' "no call fails"
  conns keepalive-close 3 "three connections"
  # Without the idle check, the closed connection is used: the request goes out, the end of input
  # comes back, and a GET is sent again on a fresh connection.
  client keepalive-close-nocheck call GET "http://127.0.0.1:18092/close-after-idle?ms=200" repeat=2 pause=500 idlecheck=off
  expect keepalive-close-nocheck 'call 1 ok status=200 .*reused=false discarded=0 .*redispatched=true' \
    "without the idle check, the GET is sent again on a fresh connection"
  # A POST is not: the server may have acted on it.
  client keepalive-close-post call POST "http://127.0.0.1:18092/close-after-idle?ms=200" body=5 repeat=2 pause=500 idlecheck=off
  expect keepalive-close-post 'call 1 error delivery=maybe delivered .*reused=true redispatched=false .*cause="the connection closed before a complete response"' \
    "without the idle check, a POST on the closed connection fails, maybe delivered"
fi

if scenario keepalive-race; then
  # The server closes the connection when the next request arrives, without answering: the request
  # crosses the server's close, which no idle check can see.
  evil keepalive-race 18093 || exit 1
  client keepalive-race call GET "http://127.0.0.1:18093/die-on-next" repeat=2
  expect keepalive-race 'call 1 ok status=200 .*reused=false .*redispatched=true' \
    "a GET whose connection closes as it is sent goes again on a fresh connection"
  logged keepalive-race 'conn1 got [0-9]+ bytes of the next request; closing without answering' \
    "the server closed the first connection on the second request"
  conns keepalive-race 2 "two connections"
  client keepalive-race-rst call GET "http://127.0.0.1:18093/die-on-next?rst=1" repeat=2
  expect keepalive-race-rst 'call 1 ok status=200 .*redispatched=true' "the same with a reset"
  client keepalive-race-post call POST "http://127.0.0.1:18093/die-on-next" body=5 repeat=2
  expect keepalive-race-post 'call 1 error delivery=maybe delivered .*reused=true redispatched=false' \
    "a POST in the same race fails, maybe delivered"
fi

if scenario idle-408; then
  # The server sends 408 and closes 100 ms after its response; the next call comes 400 ms later.
  evil idle-408 18094 || exit 1
  client idle-408 call POST "http://127.0.0.1:18094/idle-408?ms=100" body=5 repeat=2 pause=400
  expect idle-408 'call 1 ok status=200 .*reused=false discarded=1 .*redispatched=false' \
    "the idle check catches the 408 and the close; the POST goes on a new connection"
  logged idle-408 'conn1 sent 408' "the server sent the 408"
  # Without the idle check, and with the server keeping the connection open after the 408, the
  # request is written and the 408 read as its response: the POST is sent again, any method being
  # safe after a 408.
  client idle-408-nocheck call POST "http://127.0.0.1:18094/idle-408?ms=100&linger=2000" body=5 repeat=2 pause=400 idlecheck=off
  expect idle-408-nocheck 'call 1 ok status=200 .*reused=false .*redispatched=true' \
    "without the idle check, the 408 read as the response sends the POST again"
fi

if scenario close-response; then
  evil close-response 18095 || exit 1
  client close-response call GET "http://127.0.0.1:18095/close-hdr" repeat=2
  expect close-response 'call 1 ok status=200 bytes=3 .*reused=false' "a Connection: close response is not reused"
  expect close-response '^pool idle=0 checked_out=0 allocated=2$' "nothing idle"
  conns close-response 2 "two connections"
fi

if scenario head-stray; then
  evil head-stray 18096 || exit 1
  client head-stray call HEAD "http://127.0.0.1:18096/head-stray" repeat=2
  expect head-stray 'call 0 ok status=200 bytes=0 ' "the HEAD response has no body"
  expect head-stray 'call 1 ok status=200 bytes=0 .*reused=false' "stray bytes after it: not reused"
  conns head-stray 2 "two connections"
fi

if scenario concurrency; then
  evil concurrency 18097 || exit 1
  client concurrency call GET "http://127.0.0.1:18097/sleep?ms=300" concurrent=8 repeat=2
  r0=$(sed --quiet 's/^round 0 of 8 calls took ms=\([0-9]*\)\..*/\1/p' "$out/concurrency.txt")
  r1=$(sed --quiet 's/^round 1 of 8 calls took ms=\([0-9]*\)\..*/\1/p' "$out/concurrency.txt")
  if [ -n "$r0" ] && [ -n "$r1" ] && [ "$r0" -lt 900 ] && [ "$r1" -lt 900 ]; then
    result PASS concurrency "eight 300 ms calls at once take ${r0} and ${r1} ms: none waits for another"
  else
    result FAIL concurrency "rounds took ${r0:-?} and ${r1:-?} ms, expected under 900"
  fi
  expect concurrency 'summary calls n=16 .* ok=16$' "all sixteen calls succeed"
  expect concurrency '^pool idle=4 checked_out=0 allocated=12$' \
    "the first round opens eight connections and keeps four; the second reuses those and opens four"
  conns concurrency 12 "twelve connections"
  [ "$(grep --count 'reused=true' "$out/concurrency.txt")" -eq 4 ]
  if [ $? -eq 0 ]; then result PASS concurrency "four calls reused"; else result FAIL concurrency "not four calls reused"; fi
  evil concurrency-cap 18098 || exit 1
  client concurrency-cap call GET "http://127.0.0.1:18098/sleep?ms=200" concurrent=6 maxactive=2
  r0=$(sed --quiet 's/^round 0 of 6 calls took ms=\([0-9]*\)\..*/\1/p' "$out/concurrency-cap.txt")
  if [ -n "$r0" ] && [ "$r0" -ge 590 ] && [ "$r0" -lt 1200 ]; then
    result PASS concurrency-cap "six 200 ms calls with at most two at once take ${r0} ms"
  else
    result FAIL concurrency-cap "the round took ${r0:-?} ms, expected 600 to 1200"
  fi
  expect concurrency-cap 'summary calls n=6 .* ok=6$' "all six succeed"
  conns concurrency-cap 2 "two connections"
fi

if scenario pool-close; then
  evil pool-close 18099 || exit 1
  client pool-close call GET "http://127.0.0.1:18099/ok" repeat=2 close=1
  expect pool-close '^after close: pool idle=0 checked_out=0$' "closing the client closes the idle connection"
  expect pool-close 'after close: call 2 error delivery=not sent .*cause="the client closed the connection"' \
    "a call after closing fails, not sent"
  logged pool-close 'conn1 EOF from client after 2 requests' "the server sees the connection closed"
  client pool-close-off call GET "http://127.0.0.1:18099/ok" close=1 pool=0
  expect pool-close-off 'after close: call 1 error delivery=not sent .*cause="the client closed the connection"' \
    "with pooling off, too"
fi

if scenario redispatch-refused; then
  # The server goes away between two calls.  Without the idle check, the second call's GET goes out
  # on the closed connection and is sent again on a fresh connection, which is refused: the error
  # describes the second attempt, but the first was written, so it says maybe delivered.
  evil redispatch-refused 18104 || exit 1
  ( sleep 0.5; kill "${pids[-1]}" ) &
  client redispatch-refused call GET "http://127.0.0.1:18104/ok" repeat=2 pause=1000 idlecheck=off retries=0
  expect redispatch-refused 'call 1 error delivery=maybe delivered .*reused=false redispatched=true .*could not connect' \
    "a re-dispatched GET whose fresh connection is refused: maybe delivered"
fi

if scenario idle-timeout; then
  evil idle-timeout 18100 || exit 1
  client idle-timeout call GET "http://127.0.0.1:18100/ok" repeat=2 pause=600 idletimeout=300
  expect idle-timeout 'call 1 ok status=200 .*reused=false discarded=0 ' "an expired idle connection is not used"
  logged idle-timeout 'conn1 EOF from client after 1 requests' "and is closed"
  conns idle-timeout 2 "two connections"
fi

# --- The per-call planner: redirects and retries.  Ports 18110-18116.

# requests <log> <extended regex>: how many requests in a server log match.
requests() {
  grep --count --extended-regexp "$2" "$1"
}

if scenario redirect-chain; then
  evil redirect-chain 18110 || exit 1
  client redirect-chain call GET "http://127.0.0.1:18110/chain/3"
  expect redirect-chain 'call 0 ok status=200 .*hops=3 retries=0 uri=http://127\.0\.0\.1:18110/chain/0 tls=none body_start="GET /chain/0 ' \
    "three redirects within one origin, then the answer"
  conns redirect-chain 1 "the redirects and the final request share one connection"
  logged redirect-chain 'conn1 req4 GET /chain/0 ' "the server saw four requests on it"
  trace_ok redirect-chain
fi

if scenario redirect-cross; then
  evil redirect-cross 18111 || exit 1
  start redirect-cross other "listening" "$PY" -I "$here/evil.py" --port 18112 || exit 1
  other=$out/redirect-cross.other.log
  client redirect-cross call GET "http://127.0.0.1:18111/bounce/18112/echo" auth=Bearer-secret cookie=s1
  expect redirect-cross 'call 0 ok status=200 .*hops=1 .*uri=http://127\.0\.0\.1:18112/echo tls=none body_start="GET /echo auth=None cookie=None ' \
    "a redirect to another origin is followed"
  logged redirect-cross "req1 GET /bounce/18112/echo \{'authorization': \['Bearer-secret'\], 'cookie': \['s1'\], " \
    "the first origin got the Authorization and Cookie fields"
  if grep --quiet --extended-regexp "req1 GET /echo \{'host': \['127\.0\.0\.1:18112'\], 'connection': \['keep-alive'\]\} body=0B" "$other" &&
      ! grep --quiet --extended-regexp "authorization|cookie" "$other"; then
    result PASS redirect-cross "the other origin got neither, and its own Host"
  else
    result FAIL redirect-cross "the other origin's server log shows credentials or the wrong Host"
  fi
  client redirect-back call GET "http://127.0.0.1:18111/bounce/18112/bounce/18111/echo" auth=Bearer-secret cookie=s1
  expect redirect-back "call 0 ok status=200 .*hops=2 .*body_start=\"GET /echo auth=\['Bearer-secret'\] cookie" \
    "a hop back to the first origin gives the credentials back"
  trace_ok redirect-cross
  trace_ok redirect-back
fi

if scenario redirect-303; then
  evil redirect-303 18113 || exit 1
  log=$out/redirect-303.evil.log
  client redirect-303 call POST "http://127.0.0.1:18113/redir/303?to=/echo" body=11
  expect redirect-303 'call 0 ok status=200 .*hops=1 .*body_start="GET /echo ' "a 303 after a POST is followed"
  logged redirect-303 "req1 POST /redir/303\?to=/echo .*'content-length': \['11'\]\} body=11B" \
    "the POST went out with its body"
  logged redirect-303 "req2 GET /echo \{'host': \['127\.0\.0\.1:18113'\], 'connection': \['keep-alive'\]\} body=0B" \
    "and the 303 made it a GET, with no body and no Content-Length"
  client redirect-307 call POST "http://127.0.0.1:18113/redir/307?to=/echo" body=11
  expect redirect-307 "call 0 ok status=200 .*hops=1 .*body_start=\"POST /echo " "a 307 keeps the POST"
  logged redirect-303 "req2 POST /echo .*'content-length': \['11'\]\} body=11B" "redirect-307: and its body (the server is redirect-303's)"
  conns redirect-303 2 "each call sent both of its requests on one connection"
  # An https target that speaks plain HTTP: evil.py waits for a request head, which a ClientHello
  # never completes, so the handshake times out.
  client https-plain call GET "https://127.0.0.1:18113/echo" tlshs=300 retries=0
  expect https-plain 'call 0 error delivery=not sent .*cause="TLS handshake timeout"' \
    "an https request to a plain HTTP server fails in the handshake; nothing sent"
  conns redirect-303 3 "and that is one more connection"
  trace_ok redirect-303
  trace_ok redirect-307
  trace_ok https-plain
fi

if scenario redirect-limit; then
  evil redirect-limit 18114 || exit 1
  log=$out/redirect-limit.evil.log
  client redirect-limit call GET "http://127.0.0.1:18114/infinite-redirect"
  expect redirect-limit 'call 0 error delivery=response received .*hops=10 .*status=\(some 302\) cause="more than 10 redirects"' \
    "an eleventh redirect fails the call"
  n=$(requests "$log" ' req[0-9]+ GET /infinite-redirect')
  if [ "$n" -eq 11 ]; then
    result PASS redirect-limit "the server saw the request and the ten redirects followed: $n"
  else
    result FAIL redirect-limit "the server saw $n requests, expected 11"
  fi
  client redirect-limit-3 call GET "http://127.0.0.1:18114/infinite-redirect" maxredirects=3
  expect redirect-limit-3 'call 0 error .*hops=3 .*cause="more than 3 redirects"' "with maxRedirects 3, a fourth fails"
  client redirect-off call GET "http://127.0.0.1:18114/infinite-redirect" follow=0
  expect redirect-off 'call 0 ok status=302 .*hops=0 ' "with redirects off, the 302 is delivered"
  conns redirect-limit 3 "one connection per call"
  trace_ok redirect-limit
  trace_ok redirect-limit-3
  trace_ok redirect-off
fi

if scenario retry-after; then
  evil retry-after 18115 || exit 1
  log=$out/retry-after.evil.log
  client retry-503 call GET "http://127.0.0.1:18115/flaky?key=a&after=1" retry503=1
  expect retry-503 'call 0 ok status=200 .*retries=1 .*body_start="recovered after 1"' \
    "a 503 with Retry-After: 1 is retried when asked for"
  within retry-503 1000 1500 "after the 1 s it asked for"
  client retry-503-off call GET "http://127.0.0.1:18115/flaky?key=b&after=1"
  expect retry-503-off 'call 0 ok status=503 .*retries=0 ' "and delivered when not"
  client retry-429-date call GET "http://127.0.0.1:18115/flaky?key=c&code=429&after=date2" retry429=1
  expect retry-429-date 'call 0 ok status=200 .*retries=1 ' "a 429 with a Retry-After date is retried"
  within retry-429-date 1990 2600 "2 s after the response's Date"
  client retry-503-long call GET "http://127.0.0.1:18115/flaky?key=d&after=120" retry503=1
  expect retry-503-long 'call 0 ok status=503 .*retries=0 ' "a Retry-After over the 60 s limit is delivered"
  within retry-503-long 0 500 "at once"
  client retry-503-backoff call GET "http://127.0.0.1:18115/flaky?key=e&n=2" retry503=1 seed=42
  expect retry-503-backoff 'call 0 ok status=200 .*retries=2 .*body_start="recovered after 2"' \
    "without a Retry-After, the backoff"
  expect retry-503-backoff '^trace call 0 retry delays=\[23, 49\] ' "of seed 42"
  gaps_within retry-503-backoff 150
  client retry-503-post call POST "http://127.0.0.1:18115/flaky?key=f&after=1" body=5 retry503=1
  expect retry-503-post 'call 0 ok status=503 .*retries=0 ' "a POST is not sent again after a 503"
  n=$(requests "$log" ' POST /flaky\?key=f')
  [ "$n" -eq 1 ] && result PASS retry-503-post "the server saw the POST once" || result FAIL retry-503-post "the server saw the POST $n times"
  for s in retry-503 retry-503-off retry-429-date retry-503-long retry-503-backoff retry-503-post; do trace_ok $s; done
fi

if scenario no-resend; then
  evil no-resend 18116 || exit 1
  log=$out/no-resend.evil.log
  # The server reads the request and resets the connection: it may have acted on it.
  client no-resend-post call POST "http://127.0.0.1:18116/rst" body=5
  expect no-resend-post 'call 0 error delivery=maybe delivered .*retries=0 not_retried=LeanHttp.Call.NoRetry.delivered ' \
    "a POST that may have been delivered is not sent again"
  n=$(requests "$log" ' POST /rst ')
  [ "$n" -eq 1 ] && result PASS no-resend-post "the server saw it once" || result FAIL no-resend-post "the server saw it $n times"
  client no-resend-get call GET "http://127.0.0.1:18116/rst"
  expect no-resend-get 'call 0 error delivery=maybe delivered .*retries=2 not_retried=LeanHttp.Call.NoRetry.hopLimit ' \
    "a GET is sent again, twice"
  n=$(requests "$log" ' GET /rst ')
  [ "$n" -eq 3 ] && result PASS no-resend-get "the server saw it three times" || result FAIL no-resend-get "the server saw it $n times"
  trace_ok no-resend-post
  trace_ok no-resend-get
fi

if scenario drain-limit; then
  # A redirect or retried response whose body is longer than the drain limit costs its connection.
  evil drain-limit 18120 || exit 1
  client drain-redirect call GET "http://127.0.0.1:18120/redir/302?to=/echo&pad=200000"
  expect drain-redirect 'call 0 ok status=200 .*hops=1 .*body_start="GET /echo ' "a redirect with a 200 KB body is followed"
  client drain-retry call GET "http://127.0.0.1:18120/flaky?key=g&after=0&pad=200000" retry503=1
  expect drain-retry 'call 0 ok status=200 .*retries=1 ' "a 503 with a 200 KB body is retried"
  conns drain-limit 4 "each call needed a second connection: the long bodies were not drained"
  trace_ok drain-redirect
  trace_ok drain-retry
fi

if scenario redispatch-408; then
  # A POST answered on its reused connection by a 408 the server sent while it was idle (no idle
  # check), sent again on a fresh connection, which is refused (the server stopped listening after
  # the 408): the call's error must not say not sent, since the first request was written.
  evil redispatch-408 18119 || exit 1
  client redispatch-408 call POST "http://127.0.0.1:18119/idle-408?ms=100&linger=5000&unlisten=1" body=5 repeat=2 pause=400 idlecheck=off retries=0
  expect redispatch-408 'call 1 error delivery=maybe delivered .*redispatched=true .*could not connect' \
    "the re-dispatched POST is refused, and the error says maybe delivered"
  logged redispatch-408 'stopped listening' "the server stopped listening after its 408"
  trace_ok redispatch-408
fi

# --- Streaming (`Client.withResponse`).  Ports 18117-18118.

# rss_kb <scenario>: the peak resident memory net-client reported, in kB.
rss_kb() {
  sed --quiet 's/^rss_peak_kb=\([0-9]*\) .*/\1/p' "$out/$1.txt"
}

if scenario stream-big; then
  evil stream-big 18117 || exit 1
  client stream-big stream GET "http://127.0.0.1:18117/bigbody?n=200000000" pull=4096
  expect stream-big 'stream 0 ok status=200 read=200000000 .* max_pull=4096 ' "a 200 MB body read in pulls of 4 KiB"
  rss=$(rss_kb stream-big)
  if [ -n "$rss" ] && [ "$rss" -lt 102400 ]; then
    result PASS stream-big "peak resident memory ${rss} kB, under 100 MB"
  else
    result FAIL stream-big "peak resident memory ${rss:-?} kB, expected under 100 MB"
  fi
  # The control: the same body read whole is held in memory, which the measurement must see.
  client stream-big-whole stream GET "http://127.0.0.1:18117/bigbody?n=200000000" whole=1 maxbody=300000000
  expect stream-big-whole 'call 0 ok status=200 bytes=200000000 ' "the control reads the body whole"
  rss=$(rss_kb stream-big-whole)
  if [ -n "$rss" ] && [ "$rss" -gt 200000 ]; then
    result PASS stream-big-whole "control: read whole, peak resident memory ${rss} kB"
  else
    result FAIL stream-big-whole "control: peak resident memory ${rss:-?} kB; the measurement cannot see the body"
  fi
  trace_ok stream-big
fi

if scenario stream-abandon; then
  evil stream-abandon 18118 || exit 1
  # Leaving the callback after the first read of a 10 MB body: too much to drain, so the connection
  # is closed, and the next call opens another.
  client stream-abandon stream GET "http://127.0.0.1:18118/bigbody?n=10000000" stop=1 repeat=2
  expect stream-abandon 'stream 0 ok status=200 read=[0-9]+ .*conn=\(some 0\) reused=false ' "the first call reads one piece and leaves"
  expect stream-abandon '^after stream 0: pool idle=0 checked_out=0 allocated=1$' "its connection is closed, not pooled"
  expect stream-abandon 'stream 1 ok status=200 .*conn=\(some 1\) reused=false ' "the next call opens a new one"
  logged stream-abandon 'conn1 (bigbody send failed|EOF from client)' "the server sees the first connection closed"
  # A body of 10 bytes whose last 7 come 30 ms after the first 3: leaving after the first read, the
  # rest is drained within the 100 ms drain limit, and the connection reused.
  client stream-drain stream GET "http://127.0.0.1:18118/stall-body?ms=30" stop=1 repeat=2
  expect stream-drain 'stream 0 ok status=200 read=3 ' "the first call reads the first 3 bytes and leaves"
  expect stream-drain '^after stream 0: pool idle=1 checked_out=0 allocated=1$' "the rest is drained and the connection kept"
  expect stream-drain 'stream 1 ok status=200 read=3 .*conn=\(some 0\) reused=true ' "and reused"
  # When the rest comes 400 ms later, past the drain limit, the connection is closed.
  client stream-drain-late stream GET "http://127.0.0.1:18118/stall-body?ms=400" stop=1 repeat=2
  expect stream-drain-late '^after stream 0: pool idle=0 checked_out=0 allocated=1$' "a rest that comes too late: the connection is closed"
  expect stream-drain-late 'stream 1 ok status=200 read=3 .*conn=\(some 1\) reused=false ' "and the next call opens another"
  within stream-drain-late 0 300 "leaving waited no more than the drain limit"
  # A body that arrived in full with the head, longer than the drain limit, left without a read:
  # nothing remains on the connection, which is kept.
  client stream-unread-big stream GET "http://127.0.0.1:18118/unread-body?n=30000" stop=0 drainbytes=1000 repeat=2
  expect stream-unread-big 'stream 1 ok status=200 read=0 .*conn=\(some 0\) reused=true ' "a body that has arrived in full keeps the connection, whatever the drain limit"
  # A body already read in full but left unread by the caller keeps the connection.
  client stream-unread stream GET "http://127.0.0.1:18118/unread-body?n=20000" stop=1 pull=1000 repeat=2
  expect stream-unread 'stream 1 ok status=200 read=1000 .*conn=\(some 0\) reused=true ' "a body read in full and left unread keeps the connection"
  # An exception inside the callback releases the connection the same way, and goes on.
  client stream-throw stream GET "http://127.0.0.1:18118/stall-body?ms=30" stop=1 throw=1
  expect stream-throw 'stream 0 threw "thrown inside the callback"' "the callback's exception reaches the caller"
  expect stream-throw '^after stream 0: pool idle=1 checked_out=0 allocated=1$' "after the connection was drained and kept"
  client stream-throw-big stream GET "http://127.0.0.1:18118/bigbody?n=10000000" stop=1 throw=1
  expect stream-throw-big '^after stream 0: pool idle=0 checked_out=0 allocated=1$' "or closed"
  # The stream refuses to be used after the callback.
  client stream-escape stream GET "http://127.0.0.1:18118/ok" stop=0 escape=1
  expect stream-escape 'after the callback: read raised ".*used after the callback of Client.withResponse ended"' \
    "a read after the callback raises an error"
  # An error while the body is read is the call's error.
  client stream-error stream GET "http://127.0.0.1:18118/cl-mismatch"
  expect stream-error 'stream call 0 error delivery=response received .*status=\(some 200\) cause="the connection closed before a complete response"' \
    "a body cut short is the call's error, with the status"
  # Body bytes that arrive with the head, before a malformed chunk in the same read, are read first.
  client stream-badchunk stream GET "http://127.0.0.1:18118/badchunk"
  expect stream-badchunk 'stream call 0 error delivery=response received .*status=\(some 200\) cause="invalid response: Bad message" .* read_before=5$' \
    "the five bytes before the malformed chunk are read, then the error"
  # Redirects are followed before the callback: it sees only the final response.
  client stream-redirect stream GET "http://127.0.0.1:18118/chain/2"
  expect stream-redirect 'stream 0 ok status=200 read=[0-9]+ .*hops=2 ' "the callback gets the response after two redirects"
  # A read in progress in another task when the callback ends: its receive is cancelled, the
  # callback's end waits for it, and the connection is released before withResponse returns.
  client stream-race stream GET "http://127.0.0.1:18118/trickle?ms=500" race=100 pull=1
  expect stream-race 'stream 0 ok status=200 read=0 ' "the callback leaves while the other task reads"
  expect stream-race '^when withResponse returned: pool checked_out=0$' "the connection was released first"
  expect stream-race 'the racing reader raised ".*used after the callback of Client.withResponse ended"' \
    "and the other task's read fails"
  within stream-race 90 400 "without waiting for the next byte of the body"
  # The call's deadline covers reading the body.
  client stream-deadline stream GET "http://127.0.0.1:18118/trickle?ms=100" deadline=1000 pull=1
  expect stream-deadline 'stream call 0 error delivery=response received .*status=\(some 200\) cause="deadline timeout"' \
    "a body still coming at the deadline fails the call"
  within stream-deadline 990 1400 "at the 1 s deadline"
  for s in stream-abandon stream-drain stream-drain-late stream-unread-big stream-unread stream-throw stream-throw-big stream-escape stream-error stream-badchunk stream-redirect stream-race stream-deadline; do trace_ok $s; done
fi

# TLS.  The certificates are made at test time by tests/net/tls-certs.sh (a test CA, server
# certificates for the right name, a wrong name, an untrusted CA and an expired one); tls.py serves
# HTTPS with one of them on its port and plain HTTP on the next.  The client trusts the test CA
# through ca=<file> (Config.tls.caFile) unless a check says otherwise.  Every client run is also
# checked for a prompt exit, as everywhere.
tls_server() { # tls_server <scenario> <port> <certificate> [tls.py options...]
  local scenario=$1 port=$2 cert=$3; shift 3
  start "$scenario" tls "listening" "$PY" -I "$here/tls.py" --cert "$certs/$cert.pem" \
    --key "$certs/$cert.key" --port "$port" --plain-port $((port + 1)) "$@"
}

# tls_conns <scenario> <count> <description>: the scenario's TLS server accepted <count> connections.
tls_conns() {
  local got
  got=$(grep --count '^ *[0-9.]* conn[0-9]* accepted from ' "$out/$1.tls.log")
  if [ "$got" -eq "$2" ]; then
    result PASS "$1" "$3: $got"
  else
    result FAIL "$1" "$3: $got, expected $2"
  fi
}

if scenario tls-get; then
  tls_server tls-get 18130 good || exit 1
  client tls-get call GET "https://127.0.0.1:18130/hello" ca="$certs/ca.pem"
  expect tls-get 'call 0 ok status=200 bytes=15 .*uri=https://127\.0\.0\.1:18130/hello tls=TLSv1\.3 body_start="hello over tls' \
    "a GET over TLS 1.3, verified against the test CA"
  client tls-post call POST "https://127.0.0.1:18130/echo" body=100000 ca="$certs/ca.pem"
  expect tls-post 'call 0 ok status=200 bytes=100000 .*tls=TLSv1\.3' "a POST of 100 KB over TLS, echoed"
  client tls-big call GET "https://127.0.0.1:18130/big?n=50000000" ca="$certs/ca.pem"
  expect tls-big 'call 0 ok status=200 bytes=50000000 .*tls=TLSv1\.3' "a 50 MB body over TLS"
  within tls-big 0 5000 "in less than 5 s"
  client tls-localhost call GET "https://localhost:18130/hello" ca="$certs/ca.pem"
  expect tls-localhost 'call 0 ok status=200 .*tls=TLSv1\.3' "a host name matches the certificate's DNS name"
  if grep --quiet --extended-regexp "conn[0-9]+ GET /hello \{'host': 'localhost:18130', 'connection': 'keep-alive'\}" "$out/tls-get.tls.log"; then
    result PASS tls-localhost "the server got Host: localhost:18130"
  else
    result FAIL tls-localhost "the server did not log the request to localhost"
  fi
  # SNI: the host name for localhost, nothing for the IP literals (RFC 6066 section 3).
  if [ "$(grep --count 'sni=localhost$' "$out/tls-get.tls.log")" -eq 1 ] &&
      [ "$(grep --count 'sni=None$' "$out/tls-get.tls.log")" -eq 3 ]; then
    result PASS tls-localhost "SNI carried localhost, and nothing for the three calls to 127.0.0.1"
  else
    result FAIL tls-localhost "the server's log of SNI: $(grep --only-matching 'sni=.*' "$out/tls-get.tls.log" | tr '\n' ' ')"
  fi
  if grep --quiet "alpn=http/1.1" "$out/tls-get.tls.log"; then
    result PASS tls-get "the client offered ALPN http/1.1"
  else
    result FAIL tls-get "the server saw no ALPN http/1.1"
  fi
  trace_ok tls-get
  trace_ok tls-post
fi

if scenario tls-reuse; then
  tls_server tls-reuse 18132 good || exit 1
  client tls-reuse call GET "https://127.0.0.1:18132/hello" ca="$certs/ca.pem" repeat=3
  expect tls-reuse 'call 2 ok status=200 .*conn=\(some 0\) reused=true .*tls=TLSv1\.3' \
    "the third call reuses the first call's TLS connection"
  tls_conns tls-reuse 1 "one TLS connection for three calls"
  client tls-nopool call GET "https://127.0.0.1:18132/hello" ca="$certs/ca.pem" repeat=2 pool=0
  expect tls-nopool 'call 1 ok status=200 .*reused=false' "with pooling off, every call has its own"
  tls_conns tls-reuse 3 "and the server saw two more"
  trace_ok tls-reuse
fi

if scenario tls-verify; then
  tls_server tls-verify 18134 wrong || exit 1
  client tls-wrong-ip call GET "https://127.0.0.1:18134/hello" ca="$certs/ca.pem"
  expect tls-wrong-ip 'call 0 error delivery=not sent .*not_retried=LeanHttp.Call.NoRetry.cause .*cause="TLS certificate verification failed: IP address mismatch"' \
    "a certificate without the address is refused, not retried, nothing sent"
  client tls-wrong-name call GET "https://localhost:18134/hello" ca="$certs/ca.pem"
  expect tls-wrong-name 'call 0 error delivery=not sent .*cause="TLS certificate verification failed: hostname mismatch"' \
    "a certificate for another name is refused"
  tls_conns tls-verify 2 "one connection for each, no retry"
  tls_server tls-untrusted 18136 untrusted || exit 1
  client tls-untrusted call GET "https://127.0.0.1:18136/hello" ca="$certs/ca.pem"
  expect tls-untrusted 'call 0 error delivery=not sent .*not_retried=LeanHttp.Call.NoRetry.cause .*cause="TLS certificate verification failed: unable to get local issuer certificate"' \
    "a certificate from a CA the client does not trust is refused"
  tls_server tls-expired 18138 expired || exit 1
  client tls-expired call GET "https://127.0.0.1:18138/hello" ca="$certs/ca.pem"
  expect tls-expired 'call 0 error delivery=not sent .*cause="TLS certificate verification failed: certificate has expired"' \
    "an expired certificate is refused"
  # Without the test CA the system's trust store is used, which does not hold it.
  client tls-system call GET "https://127.0.0.1:18136/hello"
  expect tls-system 'call 0 error delivery=not sent .*cause="TLS certificate verification failed: unable to get local issuer certificate"' \
    "the system's trust store does not trust the test CA"
  for s in tls-wrong-ip tls-wrong-name tls-untrusted tls-expired tls-system; do trace_ok $s; done
fi

if scenario tls-trust; then
  tls_server tls-trust 18140 good || exit 1
  export SSL_CERT_FILE="$certs/ca.pem"
  client tls-trust-env call GET "https://127.0.0.1:18140/hello"
  unset SSL_CERT_FILE
  expect tls-trust-env 'call 0 ok status=200 .*tls=TLSv1\.3' "SSL_CERT_FILE names the trust store"
  export SSL_CERT_FILE=/nonexistent.pem
  client tls-trust-missing call GET "https://127.0.0.1:18140/hello"
  unset SSL_CERT_FILE
  expect tls-trust-missing 'call 0 error delivery=not sent .*not_retried=LeanHttp.Call.NoRetry.cause .*cause="TLS setup failed: SSL_CERT_FILE names /nonexistent\.pem, which is not a file"' \
    "an SSL_CERT_FILE that names nothing is a setup error, not a reason to look elsewhere"
  client tls-trust-badfile call GET "https://127.0.0.1:18140/hello" ca=/nonexistent.pem
  expect tls-trust-badfile 'call 0 error delivery=not sent .*cause="TLS setup failed: .*cannot load the CA file /nonexistent\.pem' \
    "a caFile that cannot be loaded is a setup error"
  tls_conns tls-trust 1 "setup errors open no connection"
  # A directory with OpenSSL's hashed names, as SSL_CERT_DIR.
  mkdir --parents "$certs/dir" && cp "$certs/ca.pem" "$certs/dir/" && openssl rehash "$certs/dir" > /dev/null 2>&1
  export SSL_CERT_DIR="$certs/dir"
  client tls-trust-dir call GET "https://127.0.0.1:18140/hello"
  unset SSL_CERT_DIR
  expect tls-trust-dir 'call 0 ok status=200 .*tls=TLSv1\.3' "SSL_CERT_DIR names a directory holding the test CA"
  client tls-trust-leaf call GET "https://127.0.0.1:18140/hello" ca="$certs/good.pem"
  expect tls-trust-leaf 'call 0 ok status=200 .*tls=TLSv1\.3' "the server's own certificate may anchor its chain"
fi

if scenario tls-close; then
  tls_server tls-close 18142 good || exit 1
  client tls-close-delimited call GET "https://127.0.0.1:18142/close-delimited" ca="$certs/ca.pem"
  expect tls-close-delimited 'call 0 ok status=200 bytes=100000 ' "a body ended by close_notify is complete"
  client tls-truncated call GET "https://127.0.0.1:18142/truncate" ca="$certs/ca.pem"
  expect tls-truncated 'call 0 error delivery=response received .*status=\(some 200\) cause="the connection closed before a complete response" detail=".*without close_notify, so the response may be truncated' \
    "a body ended by the connection without close_notify is truncated, and the error says so"
  client tls-truncated-framed call GET "https://127.0.0.1:18142/truncate-framed" ca="$certs/ca.pem"
  expect tls-truncated-framed 'call 0 ok status=200 bytes=10000 ' \
    "a complete Content-Length body is unaffected by a close without close_notify"
  client tls-truncated-midbody call GET "https://127.0.0.1:18142/truncate-midbody" ca="$certs/ca.pem"
  expect tls-truncated-midbody 'call 0 error delivery=response received .*cause="the connection closed before a complete response" detail=".*without close_notify' \
    "a Content-Length body cut short without close_notify fails"
  for s in tls-close-delimited tls-truncated tls-truncated-framed tls-truncated-midbody; do trace_ok $s; done
fi

if scenario tls-stray; then
  tls_server tls-stray 18144 good || exit 1
  client tls-stray call GET "https://127.0.0.1:18144/stray" ca="$certs/ca.pem" repeat=2
  expect tls-stray 'call 0 ok status=200 bytes=6 .*body_start="stray' "a response followed by stray bytes in a record of their own"
  expect tls-stray 'call 1 ok status=200 bytes=6 .*conn=\(some 1\) ' \
    "the connection with stray bytes is not reused: the second call has a connection of its own"
  tls_conns tls-stray 2 "two connections"
  trace_ok tls-stray
fi

if scenario tls-redirect; then
  tls_server tls-redirect 18146 good || exit 1
  client tls-redirect-down call GET "https://127.0.0.1:18146/redirect-http" ca="$certs/ca.pem" auth=Bearer-secret
  expect tls-redirect-down 'call 0 ok status=200 .*hops=1 .*uri=http://127\.0\.0\.1:18147/plain tls=none body_start="plain hello' \
    "a redirect from https to http is followed"
  if grep --quiet "plain[0-9]* GET /plain {'host': '127.0.0.1:18147', 'connection': 'keep-alive'}" "$out/tls-redirect.tls.log"; then
    result PASS tls-redirect-down "and the http origin got no Authorization"
  else
    result FAIL tls-redirect-down "the http origin's log shows credentials, or no request"
  fi
  evil tls-redirect-up 18148 || exit 1
  client tls-redirect-up call GET "http://127.0.0.1:18148/redir/302?to=https://127.0.0.1:18146/hello" ca="$certs/ca.pem"
  expect tls-redirect-up 'call 0 ok status=200 .*hops=1 .*uri=https://127\.0\.0\.1:18146/hello tls=TLSv1\.3' \
    "a redirect from http to https is followed, over TLS"
  trace_ok tls-redirect-down
  trace_ok tls-redirect-up
fi

if scenario tls-handshake; then
  tls_server tls-hang 18150 good --mode hang || exit 1
  client tls-hang call GET "https://127.0.0.1:18150/hello" ca="$certs/ca.pem" tlshs=500 retries=1 seed=1
  expect tls-hang 'call 0 error delivery=not sent .*retries=1 not_retried=LeanHttp.Call.NoRetry.hopLimit .*cause="TLS handshake timeout"' \
    "a server that never answers the handshake: it times out, is retried once, nothing sent"
  within tls-hang 1000 1800 "two 500 ms handshakes and one backoff"
  tls_conns tls-hang 2 "two connections"
  client tls-hang-deadline call GET "https://127.0.0.1:18150/hello" ca="$certs/ca.pem" deadline=700
  expect tls-hang-deadline 'call 0 error delivery=not sent .*not_retried=LeanHttp.Call.NoRetry.cause .*cause="deadline timeout" detail="the deadline passed during the TLS handshake"' \
    "the deadline during the handshake is the deadline's timeout, never retried"
  within tls-hang-deadline 690 1000 "at the 700 ms deadline"
  tls_server tls-closed 18152 good --mode close-handshake || exit 1
  client tls-closed call GET "https://127.0.0.1:18152/hello" ca="$certs/ca.pem" seed=1
  expect tls-closed 'call 0 error delivery=not sent .*retries=2 not_retried=LeanHttp.Call.NoRetry.hopLimit .*cause="the connection closed during the TLS handshake' \
    "a server that closes during the handshake: retried like a refused connect, nothing sent"
  tls_conns tls-closed 3 "three connections"
  tls_server tls-version 18154 good --mode tls11 || exit 1
  client tls-version call GET "https://127.0.0.1:18154/hello" ca="$certs/ca.pem"
  expect tls-version 'call 0 error delivery=not sent .*not_retried=LeanHttp.Call.NoRetry.cause .*cause="TLS handshake failed: ' \
    "a server that offers TLS 1.1 at most is refused, not retried"
  tls_conns tls-version 1 "one connection"
  for s in tls-hang tls-hang-deadline tls-closed tls-version; do trace_ok $s; done
fi

if scenario tls-idle; then
  # Servers that close a kept connection after 200 ms of idleness, with and without close_notify.
  tls_server tls-idle-notify 18156 good --idle-close 200 --idle-notify 1 || exit 1
  client tls-idle-notify call GET "https://127.0.0.1:18156/hello" ca="$certs/ca.pem" repeat=2 pause=400
  expect tls-idle-notify 'call 1 ok status=200 .*reused=false discarded=1 ' \
    "an idle connection the server closed with close_notify is caught by the idle check"
  tls_server tls-idle-abrupt 18158 good --idle-close 200 --idle-notify 0 || exit 1
  client tls-idle-abrupt call GET "https://127.0.0.1:18158/hello" ca="$certs/ca.pem" repeat=2 pause=400
  expect tls-idle-abrupt 'call 1 ok status=200 .*reused=false discarded=1 ' \
    "and one closed without it"
  client tls-idle-nocheck call GET "https://127.0.0.1:18158/hello" ca="$certs/ca.pem" repeat=2 pause=400 idlecheck=off
  expect tls-idle-nocheck 'call 1 ok status=200 .*redispatched=true ' \
    "without the idle check, the GET on the closed connection is sent again on a fresh one"
  # The pool lets an expired idle connection go with close_notify.
  tls_server tls-idle-expire 18160 good || exit 1
  client tls-idle-expire call GET "https://127.0.0.1:18160/hello" ca="$certs/ca.pem" repeat=2 pause=300 idletimeout=100
  expect tls-idle-expire 'call 1 ok status=200 .*reused=false ' "an expired idle connection is not used"
  if grep --quiet --extended-regexp "conn1 (EOF from client|read failed)" "$out/tls-idle-expire.tls.log" &&
      ! grep --quiet "conn1 read failed" "$out/tls-idle-expire.tls.log"; then
    result PASS tls-idle-expire "and the client closed it cleanly, with close_notify"
  else
    result FAIL tls-idle-expire "the server did not see the expired connection end with close_notify"
  fi
  for s in tls-idle-notify tls-idle-abrupt tls-idle-nocheck tls-idle-expire; do trace_ok $s; done
fi

if scenario tls-latched; then
  # The response and the server's close_notify arrive in one read: the exchange finishes, reusable
  # as far as HTTP goes, but the session has seen close_notify, so the connection is not pooled.
  # With the idle check off, a pooled connection would be used and fail, and the GET be sent again.
  tls_server tls-latched 18172 good || exit 1
  client tls-latched call GET "https://127.0.0.1:18172/close-after" ca="$certs/ca.pem" repeat=2 idlecheck=off
  expect tls-latched 'call 0 ok status=200 bytes=4 ' "a response followed by close_notify in the same read"
  expect tls-latched 'call 1 ok status=200 bytes=4 .*conn=\(some 1\) reused=false discarded=0 .*redispatched=false ' \
    "the connection was not pooled: the next call opened its own, and nothing was sent again"
  tls_conns tls-latched 2 "two connections"
  trace_ok tls-latched
fi

if scenario tls-12; then
  tls_server tls-12 18170 good --mode tls12 || exit 1
  client tls12-get call GET "https://127.0.0.1:18170/hello" ca="$certs/ca.pem" repeat=3
  expect tls12-get 'call 0 ok status=200 bytes=15 .*tls=TLSv1\.2 ' "a GET over TLS 1.2"
  expect tls12-get 'call 2 ok status=200 .*conn=\(some 0\) reused=true .*tls=TLSv1\.2 ' "with the connection reused"
  client tls12-post call POST "https://127.0.0.1:18170/echo" body=100000 ca="$certs/ca.pem"
  expect tls12-post 'call 0 ok status=200 bytes=100000 .*tls=TLSv1\.2' "a POST of 100 KB over TLS 1.2"
  client tls12-close-delimited call GET "https://127.0.0.1:18170/close-delimited" ca="$certs/ca.pem"
  expect tls12-close-delimited 'call 0 ok status=200 bytes=100000 ' "a body ended by close_notify, over TLS 1.2"
  client tls12-truncated call GET "https://127.0.0.1:18170/truncate" ca="$certs/ca.pem"
  expect tls12-truncated 'call 0 error delivery=response received .*detail=".*without close_notify' \
    "and a truncated one fails"
  for s in tls12-get tls12-post tls12-close-delimited tls12-truncated; do trace_ok $s; done
fi

if scenario tls-names; then
  # A certificate naming the host only in its common name is refused: no fallback to it.
  tls_server tls-cn 18164 cn-only || exit 1
  client tls-cn-only call GET "https://localhost:18164/hello" ca="$certs/ca.pem"
  expect tls-cn-only 'call 0 error delivery=not sent .*cause="TLS certificate verification failed: hostname mismatch"' \
    "a certificate with the name only in its common name is refused"
  # A partial wildcard (w*.lh.test) is refused; a whole-label one (*.lh.test) is accepted.
  tls_server tls-wild 18166 partial-wild || exit 1
  client tls-partial-wild call GET "https://wild.lh.test:18166/hello" ca="$certs/ca.pem"
  expect tls-partial-wild 'call 0 error delivery=not sent .*cause="TLS certificate verification failed: hostname mismatch"' \
    "a partial wildcard is refused"
  tls_server tls-fullwild 18168 full-wild || exit 1
  client tls-full-wild call GET "https://wild.lh.test:18168/hello" ca="$certs/ca.pem"
  expect tls-full-wild 'call 0 ok status=200 .*tls=TLSv1\.3' "a whole-label wildcard is accepted"
  if grep --quiet "sni=wild.lh.test" "$out/tls-fullwild.tls.log"; then
    result PASS tls-full-wild "SNI carried the name"
  else
    result FAIL tls-full-wild "the server saw no SNI wild.lh.test"
  fi
  for s in tls-cn-only tls-partial-wild tls-full-wild; do trace_ok $s; done
fi

if scenario tls-stream; then
  # Streamed bodies over TLS: a body left early, a read in another task when the callback ends,
  # an exception in the callback, and a whole body in small pulls.
  tls_server tls-stream 18162 good || exit 1
  client tls-stream-abandon stream GET "https://127.0.0.1:18162/big?n=10000000" ca="$certs/ca.pem" stop=1 repeat=2
  expect tls-stream-abandon 'stream 0 ok status=200 read=[0-9]+ .*conn=\(some 0\) reused=false ' "the first call reads one piece and leaves"
  expect tls-stream-abandon '^after stream 0: pool idle=0 checked_out=0 allocated=1$' "its connection is closed, not pooled"
  expect tls-stream-abandon 'stream 1 ok status=200 .*conn=\(some 1\) reused=false ' "the next call opens a new one"
  client tls-stream-race stream GET "https://127.0.0.1:18162/trickle?ms=500" ca="$certs/ca.pem" race=100 pull=1
  expect tls-stream-race 'stream 0 ok status=200 read=0 ' "the callback leaves while the other task reads"
  expect tls-stream-race '^when withResponse returned: pool checked_out=0$' "the connection was released first"
  expect tls-stream-race 'the racing reader raised ".*used after the callback of Client.withResponse ended"' \
    "and the other task's read fails"
  within tls-stream-race 90 400 "without waiting for the next byte of the body"
  client tls-stream-throw stream GET "https://127.0.0.1:18162/big?n=10000000" ca="$certs/ca.pem" stop=1 throw=1
  expect tls-stream-throw 'stream 0 threw "thrown inside the callback"' "the callback's exception reaches the caller"
  client tls-stream-pulls stream GET "https://127.0.0.1:18162/big?n=1000000" ca="$certs/ca.pem" pull=4096
  expect tls-stream-pulls 'stream 0 ok status=200 read=1000000 ' "a 1 MB body in 4 KiB pulls"
  client tls-stream-deadline stream GET "https://127.0.0.1:18162/trickle?ms=100" ca="$certs/ca.pem" deadline=1000 pull=1
  expect tls-stream-deadline 'stream call 0 error delivery=response received .*cause="deadline timeout"' \
    "a body still coming at the deadline fails the call"
  within tls-stream-deadline 990 1400 "at the 1 s deadline"
  for s in tls-stream-abandon tls-stream-race tls-stream-throw tls-stream-pulls tls-stream-deadline; do trace_ok $s; done
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
# Every call of every scenario had its steps checked against the planner.
bad=$(grep --files-with-matches 'trace call .* FAIL' "$out"/*.txt 2>/dev/null | xargs --no-run-if-empty --max-args=1 basename | tr '\n' ' ')
if [ -n "$bad" ]; then
  result FAIL traces "calls whose steps the planner does not replay, in: $bad"
else
  result PASS traces "every call's steps replay through the planner ($(cat "$out"/*.txt | grep --count 'trace call .* ok') calls)"
fi
# A name that matches no scenario, or a run with no checks at all, must not pass silently.
for s in "${selected[@]}"; do
  case " ${matched[*]} " in *" $s "*) ;; *) echo "FAIL $s: no such scenario" | tee --append "$out/summary.txt"; fails=$((fails + 1)) ;; esac
done
if [ $((passes + fails + knowns)) -eq 0 ]; then
  echo "FAIL run: no checks ran" | tee --append "$out/summary.txt"; fails=1
fi
echo "### $passes passed, $fails failed, $knowns known limitations, $skips skipped" | tee --append "$out/summary.txt"
[ "$fails" -eq 0 ]
