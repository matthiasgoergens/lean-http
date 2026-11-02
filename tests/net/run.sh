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
# tcp_syn_retries is above 2, dns-timeout when not run as root (it rewrites /etc/resolv.conf and
# listens on port 53), and timers without taskset.
#
# Writes one file per scenario to out/net/<name>.txt, each starting with the client's command and
# ending with its exit status, wall time and how long the process took to exit after `main`
# returned, plus the logs of the servers it used; prints PASS, FAIL, KNOWN or SKIP per check and a
# summary.

root=$(cd "$(dirname "$0")/../.." && pwd) || exit 1
# The exit check reads the system's clock through $EPOCHREALTIME, which bash has since version 5.
[ -n "${EPOCHREALTIME:-}" ] || { echo "tests/net/run.sh needs bash 5 or later (\$EPOCHREALTIME)" >&2; exit 1; }
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

# How long a process may take to exit after `main` returned, in ms.  The delays this exists to catch
# are an abandoned lookup holding the process until the resolver gives up (8 s and more, dns-timeout)
# and a receive left pending at exit (a hang).  A correct client usually exits within milliseconds;
# on a loaded host (load average 300 to 400 on 128 CPUs) it took up to about a second, measured as
# below (NOTES.md, "The real-socket suite under load").
EXIT_MS=4000

# client <scenario> <net-client args...>: run the client once, record its output and timings.
# A non-zero exit status or a slow exit is a FAIL, or KNOWN with the reason in $known_exit.  The exit
# is timed from the moment `main` returned, by the system's clock, which the client prints
# (returning_unix_us) and bash reads without starting a process ($EPOCHREALTIME), to the moment the
# shell sees the process end; the process's start, until `main` began, is recorded as well
# (start_ms) but not checked.
client() {
  local scenario=$1; shift
  local file="$out/$scenario.txt"
  echo "\$ net-client $*" > "$file"
  local t0 t1 rc
  t0=${EPOCHREALTIME/[.,]/}
  timeout 60 "$BIN" "$@" >> "$file" 2>&1
  rc=$?
  t1=${EPOCHREALTIME/[.,]/}
  local wall=$(( (t1 - t0) / 1000 ))
  local began returned
  began=$(sed --quiet 's/^main returning at .* started_unix_us=\([0-9]*\) .*/\1/p' "$file")
  returned=$(sed --quiet 's/^main returning at .* returning_unix_us=\([0-9]*\)$/\1/p' "$file")
  if [ -z "$returned" ]; then
    echo "exit status=$rc wall_ms=$wall" >> "$file"
    result FAIL "$scenario" "main never returned (status $rc)"
    return
  fi
  local after=$(( (t1 - returned) / 1000 )) start=$(( (began - t0) / 1000 ))
  echo "exit status=$rc wall_ms=$wall start_ms=$start exit_after_main_ms=$after" >> "$file"
  if { [ "$after" -gt "$EXIT_MS" ] || [ "$rc" -ne 0 ]; } && [ -n "${known_exit:-}" ]; then
    result KNOWN "$scenario" "exit status $rc, ${after} ms after main returned: $known_exit"
  elif [ "$rc" -ne 0 ]; then
    result FAIL "$scenario" "exit status $rc, ${after} ms after main returned"
  elif [ "$after" -gt "$EXIT_MS" ]; then
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

# How late a correct client may end a wait on a loaded host, in ms.  On the shared build host, with
# three CI runs at once and other people's jobs (load average 110 to 270 on 128 CPUs), calls timed
# from their start ended up to 470 ms past their time; at load average 300 to 480, up to 2.2 s.
# Every check of a time is "no earlier than the time (less up to 10 ms of rounding), and no later
# than the time plus SLACK", and its scenario is arranged so that what a broken client would do
# instead (not time out at all, wait for the server, wait for the rest of a body, wait twice as long)
# takes longer than that: a broken client cannot be faster than the server or the timer it waits
# for, however idle the host.  The medians of blackhole-first (240 to 600 ms), blackhole-stagger50
# (40 to 200) and nodelay (under 20) keep tighter bounds, which they need to tell a 250 ms stagger
# from a 50 ms one and a 40 ms stall from none: a median of ten or more calls is not moved by a few
# slow ones (at load average 300 to 600 it stayed within 80 ms of an idle host's).
SLACK=3000

# call_ms <scenario>: the time of the first call, in whole milliseconds.
call_ms() {
  sed --quiet 's/^\(stream \|upload \)\{0,1\}\(call\|stream\) 0 .* ms=\([0-9]*\)\..*/\3/p' "$out/$1.txt" | head --lines=1
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

# us_of <scenario> <regex>: the time ms=N.NNN of the first line matching <regex>, in microseconds.
us_of() {
  grep --extended-regexp "$2" "$out/$1.txt" | head --lines=1 \
    | sed --quiet 's/.* ms=\([0-9]*\)\.\([0-9][0-9][0-9]\).*/\1\2/p'
}

# since <scenario> <from regex> <to regex> <lo> <hi> <description>: the first lines matching the two
# regexes have times ms=F and ms=N (both from the start of the first call), with lo <= N - F <= hi.
since() {
  local from to d
  from=$(us_of "$1" "$2")
  to=$(us_of "$1" "$3")
  if [ -z "$from" ] || [ -z "$to" ]; then
    result FAIL "$1" "$6: no time (from: ${from:-none}, to: ${to:-none})"
    return
  fi
  # Base 10: a time below 1 ms has leading zeros, which $((...)) would read as octal.
  d=$((10#$to - 10#$from))
  if [ "$d" -ge $(($4 * 1000)) ] && [ "$d" -le $(($5 * 1000)) ]; then
    result PASS "$1" "$6: $((d / 1000)) ms"
  else
    result FAIL "$1" "$6: $((d / 1000)) ms, expected $4-$5"
  fi
}

# since_fired <scenario> <regex> <lo> <hi> <description>: the first line matching <regex> has a time
# between lo and hi ms after the cancellation or shutdown fired.
since_fired() { since "$1" '^(cancel|shutdown) fired at ' "$2" "$3" "$4" "$5"; }

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
# for a loaded machine (30 ms failed under load: a timer woke up to 100 ms late, and 150 ms was
# exceeded by 137 ms on a host at load average 200).  The scenarios that use it give delays above
# SLACK, so that a retry that waited twice its delay is still caught.
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
# 18110-18120: the planner's and the streaming scenarios; 18121-18128: the upload scenarios;
# 18130-18175: the TLS scenarios (18174-18175 a streamed upload); 18180-18193: cancelling, and the
# lookups of a call

# Scenarios the environment cannot run, with the reason.
declare -A unavailable=()

# Names for the resolver tests (tests/net/hosts).  getaddrinfo without a socket type returns each of
# these addresses once per socket type, three times in all.
if ! grep --quiet 'dual\.test' /etc/hosts || ! grep --quiet 'wild\.lh\.test' /etc/hosts; then
  if [ -w /etc/hosts ]; then
    cat "$here/hosts" >> /etc/hosts || exit 1
  else
    for s in dns-dup dns-dual blackhole-first tls-names dns-once; do
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
if ! command -v taskset > /dev/null; then
  unavailable[timers]="needs taskset, to hold up the event loop's thread"
fi
syn_retries=$(cat /proc/sys/net/ipv4/tcp_syn_retries)
# The TLS scenarios need the openssl command-line tool to make their certificates.
certs=$out/tls-certs
if ! command -v openssl > /dev/null; then
  for s in tls-get tls-reuse tls-verify tls-trust tls-close tls-stray tls-redirect tls-handshake tls-idle \
      tls-latched tls-12 tls-names tls-stream tls-upload cancel-tls; do
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
# The suite's own errors, kept, so that an error of the script (a helper used before it is defined,
# as `since` once was, silently, for three checks) fails the run rather than vanishing into the
# console.
exec 2> >(tee "$out/stderr.txt" >&2)
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
  # abandoned ::1 attempt would close only when the kernel gives up on that attempt (7 s with
  # tcp_syn_retries=2), or at exit, 2 s and more after the next call connected, for the first calls.
  # The server's threads log the end of one connection and the start of the next, which a loaded host
  # can write out of order (once 72 ms apart), so the end must be logged no later than 1 s after the
  # next connection's start, by the log's own times.
  ordered=1
  late=""
  for k in $(seq 1 9); do
    eof=$(sed --quiet "s/^ *\([0-9]*\)\.[0-9] conn$k EOF from client.*/\1/p" "$out/blackhole-first.evil.log" | head --lines=1)
    next=$(sed --quiet "s/^ *\([0-9]*\)\.[0-9] conn$((k + 1)) accepted.*/\1/p" "$out/blackhole-first.evil.log" | head --lines=1)
    if [ -z "$eof" ] || [ -z "$next" ] || [ "$eof" -gt $((next + 1000)) ]; then
      ordered=0; late="$late conn$k(end ${eof:-never}, next ${next:-never})"
    fi
  done
  if [ $ordered -eq 1 ]; then
    result PASS blackhole-first "each call's connection closed before the next call connected"
  else
    result FAIL blackhole-first "a call's connection was still open when the next call connected:$late"
  fi
  median_within blackhole-first 240 600 "median call within about the 250 ms stagger"
  client blackhole-stagger50 call GET "http://dual.test:$DUAL/ok" repeat=10 stagger=50 pool=0
  median_within blackhole-stagger50 40 200 "with a 50 ms stagger, the median call is about 50 ms"
fi

if scenario blackhole-timeout; then
  start blackhole-timeout hole "blackhole" "$PY" -I "$here/blackhole.py" ::1 $HOLE || exit 1
  client blackhole-timeout call GET "http://[::1]:$HOLE/" connect=1000 retries=1 seed=1 linger=9000
  expect blackhole-timeout 'call 0 error delivery=not sent .*attempts=\[\[::1\]:18084#0:timedOut, \[::1\]:18084#1:timedOut\]' \
    "two connect attempts time out; nothing sent"
  # The two attempts and the 15 ms backoff of seed 1, never shorter by IO.monoMsNow (an attempt not
  # timed out would wait about 7 s, with tcp_syn_retries=2, for the kernel to give up on its SYN).
  within blackhole-timeout 2010 $((2015 + SLACK)) "two 1 s attempts and one backoff"
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
  # Seed 3 with a base and cap of 4 s gives [3670, 3728]: delays above SLACK, so that waiting twice
  # the delay is caught by the gaps.
  "$BIN" backoff 3 base=4000 cap=4000 > "$out/refused-backoff.schedule.txt" 2>&1
  client refused-backoff call GET "http://127.0.0.1:$CLOSED/" seed=3 base=4000 cap=4000
  expect refused-backoff 'call 0 error delivery=not sent .*rounds=3 lookups=0 seed=3 .*retries=2 not_retried=LeanHttp.Call.NoRetry.hopLimit .*could not connect' \
    "refused three times (two retries by the planner); nothing sent"
  expect refused-backoff 'attempts=\[127\.0\.0\.1:18085#0:failed\([^]]*\), 127\.0\.0\.1:18085#1:failed\([^]]*\), 127\.0\.0\.1:18085#2:failed\([^]]*\)\]' \
    "one connect round per attempt"
  within refused-backoff 7398 $((7398 + SLACK)) "at least the 3670 + 3728 ms of backoff for seed 3"
  expect refused-backoff '^trace call 0 retry delays=\[3670, 3728\] ' "the planner's delays are the schedule of seed 3"
  gaps_within refused-backoff $SLACK
  trace_ok refused-backoff
  # With a backoff of up to 10 s and a deadline of 5 s: seed 1 draws 6004 ms for the first retry,
  # which would reach the deadline, so the call fails at once rather than wait for it (a client that
  # waited would fail at the deadline, 5 s in, or after the backoff).
  "$BIN" backoff 1 base=10000 cap=10000 n=1 > "$out/refused-deadline.schedule.txt" 2>&1
  client refused-deadline call GET "http://127.0.0.1:$CLOSED/" seed=1 base=10000 cap=10000 deadline=5000
  expect refused-deadline 'call 0 error delivery=not sent .*rounds=1 .*retries=0 not_retried=LeanHttp.Call.NoRetry.noTime .*could not connect' \
    "a retry whose backoff would reach the deadline is not made"
  within refused-deadline 0 $SLACK "the call fails at once, not at the deadline"
  trace_ok refused-deadline
fi

if scenario deadline-trickle; then
  client deadline-trickle call GET "http://127.0.0.1:$EVIL/trickle?ms=100" deadline=2000 gap=1000
  expect deadline-trickle 'call 0 error delivery=response received .*status=\(some 200\) cause="deadline timeout"' \
    "a body trickling one byte per 100 ms ends at the deadline"
  within deadline-trickle 1990 $((2000 + SLACK)) "at the 2 s deadline"
fi

if scenario deadline-interim; then
  client deadline-interim call GET "http://127.0.0.1:$EVIL/interim-forever?ms=300" deadline=2000
  expect deadline-interim 'call 0 error delivery=maybe delivered .*cause="deadline timeout"' \
    "interim responses every 300 ms, never a final one, end at the deadline"
  within deadline-interim 1990 $((2000 + SLACK)) "at the 2 s deadline"
fi

if scenario interim-limit; then
  client interim-limit call GET "http://127.0.0.1:$EVIL/interim-forever?ms=5"
  expect interim-limit 'call 0 error delivery=maybe delivered .*cause="interim responses limit exceeded"' \
    "the eleventh interim response fails the call"
fi

if scenario read-gap; then
  # The server answers 10 s after the request, long after any gap a correct client could end.
  client read-gap call GET "http://127.0.0.1:$EVIL/stall-head?ms=10000" gap=1000 retries=0
  expect read-gap 'call 0 error delivery=maybe delivered .*cause="read timeout"' "a silent server hits the read gap"
  within read-gap 990 $((1000 + SLACK)) "after the 1 s gap"
  # A GET can be sent again after a read timeout: twice more, after backoffs of at most 100 and
  # 200 ms.
  client read-gap-retried call GET "http://127.0.0.1:$EVIL/stall-head?ms=10000" gap=1000
  expect read-gap-retried 'call 0 error delivery=maybe delivered .*retries=2 not_retried=LeanHttp.Call.NoRetry.hopLimit .*cause="read timeout"' \
    "by default the GET is tried three times"
  within read-gap-retried 2990 $((3300 + SLACK)) "three 1 s gaps and two backoffs"
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
  # An attempt that the deadline did not end would wait for its own 10 s timeout.
  within connect-deadline 1490 $((1500 + SLACK)) "at the 1.5 s deadline"
fi

if scenario write-timeout; then
  start write-timeout noread "listening" "$PY" -I "$here/noread.py" $NOREAD || exit 1
  client write-timeout call POST "http://127.0.0.1:$NOREAD/" body=32000000 gap=1000
  expect write-timeout 'call 0 error delivery=maybe delivered .*cause="write timeout" detail="[0-9]+ of 32000[0-9]+ request bytes accepted"' \
    "a peer that stops reading stalls the upload; the write gap ends it"
fi

if scenario early-response; then
  start early-response early "listening" "$PY" -I "$here/early.py" $EARLY || exit 1
  client early-response call POST "http://127.0.0.1:$EARLY/" body=32000000 gap=5000
  expect early-response 'call 0 ok status=413 bytes=3 .*body_start="big"' \
    "a server that answers 413 after the head and stops reading: the response is delivered"
  within early-response 0 $SLACK "well before the 5 s write gap"
fi

# --- Pooling.  Each scenario has an evil.py of its own, so that its log counts the connections.

# conns <scenario> <n> <description>: the scenario's server accepted exactly n connections.
# count_lines <file> <regex> <n>: the lines of <file> that match, once there are n of them or 5 s
# have passed: a server may log a connection it accepted after the client has returned, when the
# connection got no answer and a loaded host held the server up (it once wrote a line 2.4 s late).
# A file that does not exist counts 0.  It waits only for too few lines: one logged late beyond n is
# not waited for.
count_lines() {
  local got k
  for k in $(seq 100); do
    got=$(grep --count --extended-regexp "$2" "$1" 2>/dev/null)
    got=${got:-0}
    [ "$got" -ge "$3" ] && break
    sleep 0.05
  done
  echo "$got"
}

conns() {
  local got
  got=$(count_lines "$out/$1.evil.log" ' accepted from ' "$2")
  if [ "$got" -eq "$2" ]; then
    result PASS "$1" "$3: $got"
  else
    result FAIL "$1" "$3: $got, expected $2"
  fi
}

# in_flight <scenario> <n> <description>: the most requests the scenario's server held at once, from
# the request's arrival to its answer (the sleep route logs both), was exactly n.
in_flight() {
  local most
  most=$(awk '/ req[0-9]+ GET \/sleep/ { k++; if (k > m) m = k } / answering after / { k-- } END { print m + 0 }' \
    "$out/$1.evil.log")
  if [ "$most" -eq "$2" ]; then
    result PASS "$1" "$3: $most"
  else
    result FAIL "$1" "$3: $most at most, expected $2"
  fi
}

# logged <scenario> <extended regex> <description>: the scenario's server logged a match (within 5 s,
# for what it logs after the client has acted, such as the end of a connection).
logged() {
  if [ "$(count_lines "$out/$1.evil.log" "$2" 1)" -ge 1 ]; then
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
  # The server closes a connection 1 s after its last response, by when the client has pooled it; the
  # next call comes 3 s later, by when the server has closed it, with seconds of margin either way for
  # a loaded host (and the idle connections kept for a minute, so that none expires first).
  evil keepalive-close 18092 || exit 1
  client keepalive-close call GET "http://127.0.0.1:18092/close-after-idle?ms=1000" repeat=3 pause=3000 idletimeout=60000
  expect keepalive-close 'call 1 ok status=200 .*reused=false discarded=1 .*redispatched=false' \
    "the idle check finds the closed connection; the call opens a new one"
  expect keepalive-close 'call 2 ok status=200 .*reused=false discarded=1 .*redispatched=false' "and again"
  expect keepalive-close 'summary calls n=3 .* ok=3$' "no call fails"
  conns keepalive-close 3 "three connections"
  # Without the idle check, the closed connection is used: the request goes out, the end of input
  # comes back, and a GET is sent again on a fresh connection.
  client keepalive-close-nocheck call GET "http://127.0.0.1:18092/close-after-idle?ms=1000" repeat=2 pause=3000 idletimeout=60000 idlecheck=off
  expect keepalive-close-nocheck 'call 1 ok status=200 .*reused=false discarded=0 .*redispatched=true' \
    "without the idle check, the GET is sent again on a fresh connection"
  # A POST is not: the server may have acted on it.
  client keepalive-close-post call POST "http://127.0.0.1:18092/close-after-idle?ms=1000" body=5 repeat=2 pause=3000 idletimeout=60000 idlecheck=off
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
  # The server sends 408 and closes 1 s after its response; the next call comes 3 s later.
  evil idle-408 18094 || exit 1
  client idle-408 call POST "http://127.0.0.1:18094/idle-408?ms=1000" body=5 repeat=2 pause=3000 idletimeout=60000
  expect idle-408 'call 1 ok status=200 .*reused=false discarded=1 .*redispatched=false' \
    "the idle check catches the 408 and the close; the POST goes on a new connection"
  logged idle-408 'conn1 sent 408' "the server sent the 408"
  # Without the idle check, and with the server keeping the connection open after the 408, the
  # request is written and the 408 read as its response: the POST is sent again, any method being
  # safe after a 408.
  client idle-408-nocheck call POST "http://127.0.0.1:18094/idle-408?ms=1000&linger=6000" body=5 repeat=2 pause=3000 idletimeout=60000 idlecheck=off
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
  # Each call takes 3 s at the server.  That none waits for another is read from the server's log,
  # not from the time a round takes: the server has all eight requests of a round before it answers
  # any, which a loaded host does not change (a call that waited for another would reach the server
  # only after the other's answer, 3 s later).
  client concurrency call GET "http://127.0.0.1:18097/sleep?ms=3000" concurrent=8 repeat=2
  in_flight concurrency 8 "eight calls at once: the server had all eight requests of a round before answering any"
  expect concurrency 'summary calls n=16 .* ok=16$' "all sixteen calls succeed"
  expect concurrency '^pool idle=4 checked_out=0 allocated=12$' \
    "the first round opens eight connections and keeps four; the second reuses those and opens four"
  conns concurrency 12 "twelve connections"
  [ "$(grep --count 'reused=true' "$out/concurrency.txt")" -eq 4 ]
  if [ $? -eq 0 ]; then result PASS concurrency "four calls reused"; else result FAIL concurrency "not four calls reused"; fi
  evil concurrency-cap 18098 || exit 1
  # Six 2 s calls, at most two at once: the server has two requests at a time, never more, and never
  # only one, which it would with one connection at a time.
  client concurrency-cap call GET "http://127.0.0.1:18098/sleep?ms=2000" concurrent=6 maxactive=2
  in_flight concurrency-cap 2 "at most two calls at once, and two at once"
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
  # Stopped a second after it logs the first request, which it answers at once; the second call
  # comes 3 s after the first returned.
  evil redispatch-refused 18104 || exit 1
  log=$out/redispatch-refused.evil.log
  server=${pids[-1]}
  ( for _ in $(seq 600); do grep --quiet 'req1 GET /ok' "$log" && break; sleep 0.05; done
    sleep 1; kill "$server" ) &
  client redispatch-refused call GET "http://127.0.0.1:18104/ok" repeat=2 pause=3000 idletimeout=60000 idlecheck=off retries=0
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
  # Retry-After of 4 s, above SLACK, so that a retry after twice the time is caught.
  client retry-503 call GET "http://127.0.0.1:18115/flaky?key=a&after=4" retry503=1
  expect retry-503 'call 0 ok status=200 .*retries=1 .*body_start="recovered after 1"' \
    "a 503 with Retry-After: 4 is retried when asked for"
  within retry-503 4000 $((4000 + SLACK)) "after the 4 s it asked for"
  client retry-503-off call GET "http://127.0.0.1:18115/flaky?key=b&after=1"
  expect retry-503-off 'call 0 ok status=503 .*retries=0 ' "and delivered when not"
  client retry-429-date call GET "http://127.0.0.1:18115/flaky?key=c&code=429&after=date4" retry429=1
  expect retry-429-date 'call 0 ok status=200 .*retries=1 ' "a 429 with a Retry-After date is retried"
  within retry-429-date 3990 $((4000 + SLACK)) "4 s after the response's Date"
  client retry-503-long call GET "http://127.0.0.1:18115/flaky?key=d&after=120" retry503=1
  expect retry-503-long 'call 0 ok status=503 .*retries=0 ' "a Retry-After over the 60 s limit is delivered"
  within retry-503-long 0 $SLACK "at once, not after the 120 s it asked for"
  client retry-503-backoff call GET "http://127.0.0.1:18115/flaky?key=e&n=2" retry503=1 seed=3 base=4000 cap=4000
  expect retry-503-backoff 'call 0 ok status=200 .*retries=2 .*body_start="recovered after 2"' \
    "without a Retry-After, the backoff"
  expect retry-503-backoff '^trace call 0 retry delays=\[3670, 3728\] ' "of seed 3"
  gaps_within retry-503-backoff $SLACK
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
  client redispatch-408 call POST "http://127.0.0.1:18119/idle-408?ms=1000&linger=6000&unlisten=1" body=5 repeat=2 pause=3000 idletimeout=60000 idlecheck=off retries=0
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
  # A body of 10 bytes whose last 7 come 2 s after the first 3 (so that the first read gets the 3
  # alone, however slow the client): leaving after the first read, the rest is drained within a
  # drain limit of 6 s, and the connection reused.
  client stream-drain stream GET "http://127.0.0.1:18118/stall-body?ms=2000" stop=1 repeat=2 drainms=6000
  expect stream-drain 'stream 0 ok status=200 read=3 ' "the first call reads the first 3 bytes and leaves"
  expect stream-drain '^after stream 0: pool idle=1 checked_out=0 allocated=1$' "the rest is drained and the connection kept"
  expect stream-drain 'stream 1 ok status=200 read=3 .*conn=\(some 0\) reused=true ' "and reused"
  # When the rest comes 8 s later, past the default drain limit of 100 ms, the connection is closed.
  client stream-drain-late stream GET "http://127.0.0.1:18118/stall-body?ms=8000" stop=1 repeat=2
  expect stream-drain-late '^after stream 0: pool idle=0 checked_out=0 allocated=1$' "a rest that comes too late: the connection is closed"
  expect stream-drain-late 'stream 1 ok status=200 read=3 .*conn=\(some 1\) reused=false ' "and the next call opens another"
  since stream-drain-late '^callback entered at ' '^stream 0 ok ' 0 $((100 + SLACK)) \
    "leaving waited no more than the drain limit, from the callback's start, not for the rest"
  # A body that arrived in full with the head, longer than the drain limit, left without a read:
  # nothing remains on the connection, which is kept.
  client stream-unread-big stream GET "http://127.0.0.1:18118/unread-body?n=30000" stop=0 drainbytes=1000 repeat=2
  expect stream-unread-big 'stream 1 ok status=200 read=0 .*conn=\(some 0\) reused=true ' "a body that has arrived in full keeps the connection, whatever the drain limit"
  # A body already read in full but left unread by the caller keeps the connection.
  client stream-unread stream GET "http://127.0.0.1:18118/unread-body?n=20000" stop=1 pull=1000 repeat=2
  expect stream-unread 'stream 1 ok status=200 read=1000 .*conn=\(some 0\) reused=true ' "a body read in full and left unread keeps the connection"
  # An exception inside the callback releases the connection the same way, and goes on.
  client stream-throw stream GET "http://127.0.0.1:18118/stall-body?ms=2000" stop=1 throw=1 drainms=6000
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
  # callback's end waits for it, and the connection is released before withResponse returns.  The
  # body's next byte comes 8 s after the head, which a client that waited for the read would wait for.
  client stream-race stream GET "http://127.0.0.1:18118/trickle?ms=8000" race=100 pull=1
  expect stream-race 'stream 0 ok status=200 read=0 ' "the callback leaves while the other task reads"
  expect stream-race '^when withResponse returned: pool checked_out=0$' "the connection was released first"
  expect stream-race 'the racing reader raised ".*used after the callback of Client.withResponse ended"' \
    "and the other task's read fails"
  since stream-race '^callback entered at ' '^stream 0 ok ' 90 $((100 + SLACK)) \
    "from the callback's start, without waiting for the next byte of the body"
  # The call's deadline covers reading the body.  Of 3 s, so that the head has come before it on a
  # loaded host.
  client stream-deadline stream GET "http://127.0.0.1:18118/trickle?ms=100" deadline=3000 pull=1
  expect stream-deadline 'stream call 0 error delivery=response received .*status=\(some 200\) cause="deadline timeout"' \
    "a body still coming at the deadline fails the call"
  within stream-deadline 2990 $((3000 + SLACK)) "at the 3 s deadline"
  for s in stream-abandon stream-drain stream-drain-late stream-unread-big stream-unread stream-throw stream-throw-big stream-escape stream-error stream-badchunk stream-redirect stream-race stream-deadline; do trace_ok $s; done
fi

ulogged() { # ulogged <scenario> <extended regex> <description>: check the upload server's log
  if [ "$(count_lines "$out/$1.upload.log" "$2" 1)" -ge 1 ]; then
    result PASS "$1" "$3"
  else
    result FAIL "$1" "$3 (no match in the server log for: $2)"
  fi
}

ucount() { # ucount <scenario> <extended regex> <n> <description>: lines of the server's log that match
  local k
  k=$(grep --count --extended-regexp "$2" "$out/$1.upload.log")
  if [ "$k" -eq "$3" ]; then
    result PASS "$1" "$4 ($k)"
  else
    result FAIL "$1" "$4: $k, expected $3"
  fi
}

uploads() { # uploads <scenario> <port>: an upload.py for one scenario
  start "$1" upload "listening" "$PY" -I "$here/upload.py" "$2"
}

if scenario upload; then
  uploads upload 18121 || exit 1
  # A body of known size, streamed in 4 KiB chunks: sent with a Content-Length, read in full by the
  # server, and the connection kept for the next call.
  client upload upload PUT "http://127.0.0.1:18121/sink" size=1000000 chunk=4096 repeat=2
  expect upload 'upload call 0 ok status=200 .*conn=\(some 0\) reused=false .* pulls=246 produced=1000000 response="pattern=ok received=1000000 framing=length chunks=0"' \
    "a 1 MB body in 4 KiB chunks, Content-Length: every byte arrives in order"
  expect upload 'upload call 1 ok status=200 .*conn=\(some 0\) reused=true ' "the connection is reused after the upload"
  ulogged upload "PUT /sink framing=length received=1000000 .*'content-length'" "the server read a Content-Length body"
  # Of unknown size: sent chunked, one chunk on the wire per chunk produced (4000 bytes, fa0 in hex).
  client upload-chunked upload POST "http://127.0.0.1:18121/sink" size=1000000 chunk=4000 declare=none repeat=2
  expect upload-chunked 'upload call 0 ok status=200 .* pulls=251 produced=1000000 response="pattern=ok received=1000000 framing=chunked chunks=250"' \
    "a 1 MB body of unknown size in 4000-byte chunks, chunked: 250 chunks on the wire, every byte in order"
  expect upload-chunked 'upload call 1 ok status=200 .*conn=\(some [0-9]+\) reused=true ' "the connection is reused after a chunked upload"
  ulogged upload "POST /sink framing=chunked received=1000000 chunks=250 .*'transfer-encoding'" "the server decoded a chunked body"
  # An empty body of unknown size is the last chunk alone.
  client upload-empty upload POST "http://127.0.0.1:18121/sink" size=0 declare=none
  expect upload-empty 'upload call 0 ok status=200 .* pulls=1 produced=0 response="pattern=ok received=0 framing=chunked chunks=0"' \
    "an empty streamed body: the last chunk alone"
  for s in upload upload-chunked upload-empty; do trace_ok $s; done
fi

if scenario upload-big; then
  uploads upload-big 18122 || exit 1
  # 256 MiB in 16 KiB chunks: the client holds one chunk at a time.
  client upload-big upload PUT "http://127.0.0.1:18122/sink" size=268435456 chunk=16384 deadline=600000
  expect upload-big 'upload call 0 ok status=200 .* produced=268435456 response="pattern=ok received=268435456 framing=length' \
    "a 256 MiB body in 16 KiB chunks arrives whole and in order"
  rss=$(rss_kb upload-big)
  if [ -n "$rss" ] && [ "$rss" -lt 102400 ]; then
    result PASS upload-big "peak resident memory ${rss} kB, under 100 MB"
  else
    result FAIL upload-big "peak resident memory ${rss:-?} kB, expected under 100 MB"
  fi
  client upload-big-chunked upload PUT "http://127.0.0.1:18122/sink" size=268435456 chunk=16384 declare=none deadline=600000
  expect upload-big-chunked 'upload call 0 ok status=200 .* produced=268435456 response="pattern=ok received=268435456 framing=chunked chunks=16384"' \
    "and chunked"
  rss=$(rss_kb upload-big-chunked)
  if [ -n "$rss" ] && [ "$rss" -lt 102400 ]; then
    result PASS upload-big-chunked "peak resident memory ${rss} kB, under 100 MB"
  else
    result FAIL upload-big-chunked "peak resident memory ${rss:-?} kB, expected under 100 MB"
  fi
  # The control: the same body as one byte array is held in memory, which the measurement must see.
  client upload-big-bytes upload PUT "http://127.0.0.1:18122/sink" size=268435456 bytes=1 deadline=600000
  expect upload-big-bytes 'upload call 0 ok status=200 .*response="pattern=ok received=268435456 framing=length' \
    "the control sends the body as bytes"
  rss=$(rss_kb upload-big-bytes)
  if [ -n "$rss" ] && [ "$rss" -gt 262144 ]; then
    result PASS upload-big-bytes "control: as bytes, peak resident memory ${rss} kB"
  else
    result FAIL upload-big-bytes "control: peak resident memory ${rss:-?} kB; the measurement cannot see the body"
  fi
  for s in upload-big upload-big-chunked upload-big-bytes; do trace_ok $s; done
fi

if scenario upload-early; then
  start upload-early early "listening" "$PY" -I "$here/early.py" 18123 || exit 1
  # A server that answers 413 after the head and reads no more: the response is delivered while the
  # upload is stalled, and the producer is not asked for the rest.
  client upload-early upload POST "http://127.0.0.1:18123/" size=32000000 chunk=65536 gap=5000
  expect upload-early 'upload call 0 ok status=413 bytes=3 .*body_start="big"' \
    "an early 413 during a streamed upload is delivered"
  within upload-early 0 $SLACK "well before the 5 s write gap"
  produced=$(sed --quiet 's/^upload call 0 .* produced=\([0-9]*\).*/\1/p' "$out/upload-early.txt")
  if [ -n "$produced" ] && [ "$produced" -lt 32000000 ]; then
    result PASS upload-early "the upload stopped: ${produced} of 32000000 bytes produced"
  else
    result FAIL upload-early "produced ${produced:-?} bytes"
  fi
  trace_ok upload-early
fi

if scenario upload-fail; then
  uploads upload-fail 18124 || exit 1
  # A producer that raises an error fails the call: maybe delivered, not retried.
  client upload-throw upload PUT "http://127.0.0.1:18124/sink" size=1000000 chunk=4096 fail=3
  expect upload-throw 'upload call 0 error delivery=maybe delivered .*retries=0 not_retried=LeanHttp.Call.NoRetry.cause .*cause="request body: the producer failed: the producer failed on purpose".* pulls=4 produced=12288' \
    "a producer that raises at its fourth pull fails the call, maybe delivered, not retried"
  # More than declared: refused before the excess is written.
  client upload-long upload PUT "http://127.0.0.1:18124/sink" size=3000 chunk=1000 declare=2500
  expect upload-long 'upload call 0 error delivery=maybe delivered .*cause="request body: the producer gave more than the declared 2500 bytes \(3000 so far\)".* pulls=3 produced=3000' \
    "a producer that gives more than it declared fails the call"
  # Fewer than declared.
  client upload-short upload PUT "http://127.0.0.1:18124/sink" size=2000 chunk=1000 declare=3000
  expect upload-short 'upload call 0 error delivery=maybe delivered .*cause="request body: the producer ended after 2000 of the declared 3000 bytes".* pulls=3 produced=2000' \
    "a producer that ends short of what it declared fails the call"
  ucount upload-fail 'framing=length received=2500 ' 0 "the server never received more than the declared size"
  ulogged upload-fail 'EOF from client' "the server sees the connections of the failed calls closed"
  for s in upload-throw upload-long upload-short; do trace_ok $s; done
fi

if scenario upload-close; then
  uploads upload-close 18125 || exit 1
  # A server that closes mid-upload: maybe delivered, and not retried, though PUT is idempotent,
  # because the body cannot be sent again.
  client upload-close upload PUT "http://127.0.0.1:18125/close?after=100000" size=10000000 chunk=16384
  expect upload-close 'upload call 0 error delivery=maybe delivered .*retries=0 not_retried=LeanHttp.Call.NoRetry.delivered ' \
    "a PUT whose server closes mid-upload: maybe delivered, not retried"
  ucount upload-close 'PUT /close ' 1 "the server saw the request once"
  # The same PUT with its body as bytes is retried: the control for the rule above.
  client upload-close-bytes upload PUT "http://127.0.0.1:18125/close?after=100000" size=10000000 bytes=1 seed=1
  expect upload-close-bytes 'upload call 0 error delivery=maybe delivered .*retries=2 not_retried=LeanHttp.Call.NoRetry.hopLimit ' \
    "control: the PUT with a byte-array body is sent three times"
  for s in upload-close upload-close-bytes; do trace_ok $s; done
fi

if scenario upload-redirect; then
  uploads upload-redirect 18126 || exit 1
  # A 307 keeps the method and the body, which a stream cannot send again: delivered, not followed.
  client upload-307 upload POST "http://127.0.0.1:18126/307" size=100000 chunk=8192
  expect upload-307 'upload call 0 ok status=307 .*hops=0 ' "a 307 after a streamed POST is delivered, not followed"
  ucount upload-redirect 'POST /sink ' 0 "the server never saw a request to the redirect's target"
  # With the body as bytes the redirect is followed: the control.
  client upload-307-bytes upload POST "http://127.0.0.1:18126/307" size=100000 bytes=1
  expect upload-307-bytes 'upload call 0 ok status=200 .*hops=1 .*response="pattern=ok received=100000' \
    "control: with a byte-array body the 307 is followed, with the body"
  for s in upload-307 upload-307-bytes; do trace_ok $s; done
fi

if scenario upload-notsent; then
  # A streamed POST to a port where nothing listens: retried (nothing was sent), and the producer
  # never asked for anything.
  client upload-notsent upload POST "http://127.0.0.1:$CLOSED/" size=1000 seed=42
  expect upload-notsent 'upload call 0 error delivery=not sent .*retries=2 .* pulls=0 produced=0' \
    "a streamed POST that cannot connect is retried and reads nothing of the stream"
  trace_ok upload-notsent
fi

if scenario upload-redispatch; then
  evil upload-redispatch 18128 || exit 1
  # The server closes a kept-alive connection when the next request arrives: a PUT whose body is
  # bytes goes again on a fresh connection, a streamed one does not, though PUT is idempotent.  The
  # server answers 2 s after the request, so that the producer has said that the body ended by then
  # (a response that comes before that leaves the connection unpooled, and nothing to race).
  client upload-race upload PUT "http://127.0.0.1:18128/die-on-next?ms=2000" size=1000 chunk=500 repeat=2
  expect upload-race 'upload call 1 error delivery=maybe delivered .*reused=true redispatched=false .*not_retried=LeanHttp.Call.NoRetry.delivered ' \
    "a streamed PUT whose pooled connection closes as it is sent is not sent again"
  client upload-race-bytes upload PUT "http://127.0.0.1:18128/die-on-next?ms=2000" size=1000 bytes=1 repeat=2
  expect upload-race-bytes 'upload call 1 ok status=200 .*redispatched=true' \
    "control: the same PUT with a byte-array body goes again on a fresh connection"
  # A 408 the server sent while the connection was idle, read as the response (no idle check): a
  # byte-array body is sent again, whatever the method; a stream is not, and the 408 is delivered.
  client upload-408 upload POST "http://127.0.0.1:18128/idle-408?ms=1000&linger=6000" size=5 repeat=2 pause=3000 idletimeout=60000 idlecheck=off
  expect upload-408 'upload call 1 ok status=408 .*redispatched=false' \
    "a streamed POST answered by the 408 of an idle connection: delivered, not sent again"
  client upload-408-bytes upload POST "http://127.0.0.1:18128/idle-408?ms=1000&linger=6000" size=5 bytes=1 repeat=2 pause=3000 idletimeout=60000 idlecheck=off
  expect upload-408-bytes 'upload call 1 ok status=200 .*redispatched=true' \
    "control: with a byte-array body the POST goes again"
  for s in upload-race upload-race-bytes upload-408 upload-408-bytes; do trace_ok $s; done
fi

if scenario upload-exit; then
  uploads upload-exit 18127 || exit 1
  # A producer still sleeping when the call ends at its deadline: the process still exits promptly.
  client upload-exit upload PUT "http://127.0.0.1:18127/sink" size=1000 chunk=100 delay=30000 deadline=3000
  expect upload-exit 'upload call 0 error delivery=maybe delivered .*cause="deadline timeout"' \
    "a producer that does not answer: the call ends at its deadline"
  within upload-exit 2990 $((3000 + SLACK)) "at the 3 s deadline, not at the producer's 30 s"
  trace_ok upload-exit
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
  got=$(count_lines "$out/$1.tls.log" '^ *[0-9.]* conn[0-9]* accepted from ' "$2")
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
  # 200 MB, read whole: 0.7 to 2.1 s at load average 130 to 370, and 50 MB once took 5.8 s at 350; a
  # body copied at every read, as the shell once did (NOTES.md, "Nothing carried across a wait is
  # updated in place": 5.6 to 7.5 s for 60 MB), would take about a minute at this size, even idle.
  client tls-big call GET "https://127.0.0.1:18130/big?n=200000000" ca="$certs/ca.pem" maxbody=300000000
  expect tls-big 'call 0 ok status=200 bytes=200000000 .*tls=TLSv1\.3' "a 200 MB body over TLS"
  within tls-big 0 45000 "in less than 45 s"
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
  # The two handshakes' 500 ms and the 15 ms backoff of seed 1, never shorter: a timer that fires
  # early is waited again (NOTES.md, "Timers fire early"); without a handshake timeout the call would
  # wait for the server forever.
  within tls-hang 1010 $((1015 + SLACK)) "two 500 ms handshakes and one backoff"
  tls_conns tls-hang 2 "two connections"
  client tls-hang-deadline call GET "https://127.0.0.1:18150/hello" ca="$certs/ca.pem" deadline=3000
  expect tls-hang-deadline 'call 0 error delivery=not sent .*not_retried=LeanHttp.Call.NoRetry.cause .*cause="deadline timeout" detail="the deadline passed during the TLS handshake"' \
    "the deadline during the handshake is the deadline's timeout, never retried"
  within tls-hang-deadline 2990 $((3000 + SLACK)) "at the 3 s deadline, not at the 10 s handshake timeout"
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
  # Servers that close a kept connection after 1 s of idleness, with and without close_notify; the
  # next call comes 3 s later.
  tls_server tls-idle-notify 18156 good --idle-close 1000 --idle-notify 1 || exit 1
  client tls-idle-notify call GET "https://127.0.0.1:18156/hello" ca="$certs/ca.pem" repeat=2 pause=3000 idletimeout=60000
  expect tls-idle-notify 'call 1 ok status=200 .*reused=false discarded=1 ' \
    "an idle connection the server closed with close_notify is caught by the idle check"
  tls_server tls-idle-abrupt 18158 good --idle-close 1000 --idle-notify 0 || exit 1
  client tls-idle-abrupt call GET "https://127.0.0.1:18158/hello" ca="$certs/ca.pem" repeat=2 pause=3000 idletimeout=60000
  expect tls-idle-abrupt 'call 1 ok status=200 .*reused=false discarded=1 ' \
    "and one closed without it"
  client tls-idle-nocheck call GET "https://127.0.0.1:18158/hello" ca="$certs/ca.pem" repeat=2 pause=3000 idletimeout=60000 idlecheck=off
  expect tls-idle-nocheck 'call 1 ok status=200 .*redispatched=true ' \
    "without the idle check, the GET on the closed connection is sent again on a fresh one"
  # The pool lets an expired idle connection go with close_notify.
  tls_server tls-idle-expire 18160 good || exit 1
  client tls-idle-expire call GET "https://127.0.0.1:18160/hello" ca="$certs/ca.pem" repeat=2 pause=300 idletimeout=100
  expect tls-idle-expire 'call 1 ok status=200 .*reused=false ' "an expired idle connection is not used"
  count_lines "$out/tls-idle-expire.tls.log" "conn1 (EOF from client|read failed)" 1 > /dev/null
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
  client tls-stream-race stream GET "https://127.0.0.1:18162/trickle?ms=8000" ca="$certs/ca.pem" race=100 pull=1
  expect tls-stream-race 'stream 0 ok status=200 read=0 ' "the callback leaves while the other task reads"
  expect tls-stream-race '^when withResponse returned: pool checked_out=0$' "the connection was released first"
  expect tls-stream-race 'the racing reader raised ".*used after the callback of Client.withResponse ended"' \
    "and the other task's read fails"
  since tls-stream-race '^callback entered at ' '^stream 0 ok ' 90 $((100 + SLACK)) \
    "from the callback's start, without waiting for the next byte of the body"
  client tls-stream-throw stream GET "https://127.0.0.1:18162/big?n=10000000" ca="$certs/ca.pem" stop=1 throw=1
  expect tls-stream-throw 'stream 0 threw "thrown inside the callback"' "the callback's exception reaches the caller"
  client tls-stream-pulls stream GET "https://127.0.0.1:18162/big?n=1000000" ca="$certs/ca.pem" pull=4096
  expect tls-stream-pulls 'stream 0 ok status=200 read=1000000 ' "a 1 MB body in 4 KiB pulls"
  # Twenty bytes, one every 500 ms: the body would end 10 s in.
  client tls-stream-deadline stream GET "https://127.0.0.1:18162/trickle?ms=500" ca="$certs/ca.pem" deadline=3000 pull=1
  expect tls-stream-deadline 'stream call 0 error delivery=response received .*cause="deadline timeout"' \
    "a body still coming at the deadline fails the call"
  within tls-stream-deadline 2990 $((3000 + SLACK)) "at the 3 s deadline"
  for s in tls-stream-abandon tls-stream-race tls-stream-throw tls-stream-pulls tls-stream-deadline; do trace_ok $s; done
fi

if scenario tls-upload; then
  tls_server tls-upload 18174 good || exit 1
  # A streamed body over TLS: of known size, then chunked, every byte checked by the server, and the
  # connection reused after each.
  client tls-upload upload PUT "https://127.0.0.1:18174/count" size=1000000 chunk=4096 ca="$certs/ca.pem" repeat=2
  expect tls-upload 'upload call 0 ok status=200 .*tls=TLSv1\.3 .* pulls=246 produced=1000000 response="pattern=ok received=1000000 framing=length"' \
    "a 1 MB streamed body over TLS, Content-Length: every byte arrives in order"
  expect tls-upload 'upload call 1 ok status=200 .*conn=\(some 0\) reused=true ' "the TLS connection is reused after it"
  client tls-upload-chunked upload PUT "https://127.0.0.1:18174/count" size=1000000 chunk=4000 declare=none ca="$certs/ca.pem" repeat=2
  expect tls-upload-chunked 'upload call 0 ok status=200 .*tls=TLSv1\.3 .* pulls=251 produced=1000000 response="pattern=ok received=1000000 framing=chunked"' \
    "and chunked"
  expect tls-upload-chunked 'upload call 1 ok status=200 .*reused=true ' "the TLS connection is reused after a chunked upload"
  for s in tls-upload tls-upload-chunked; do trace_ok $s; done
fi

# --- Cancelling a call.  Each run gives its calls a token that it cancels (cancel=MS) or shuts the
# client down (shutdown=MS), and the suite checks the error, when the call returned, what became of
# its connection, the record of its steps and, as for every run, that the process exited promptly
# after main.  The cancellation is placed at the stage of the call that the scenario is about, not
# at a time from the start, which a loaded host can stretch: MS ms after a step the client reports
# (after=send, follow, wait, deliver, read), inside the callback's or the producer's own sleep
# (after=idle, hold, pull), or once a server's log says that the request, its body or the
# ClientHello arrived (log=, logtext=).  Only where nothing can see the stage (a connect attempt
# that hangs, a lookup) is it a time, from the step before.  Whether the call returned at the
# cancellation is measured from the moment it fired (since_fired), within 1500 ms: every other way
# the call could end (the server's answer, the end of a backoff, a timeout, the producer's stall) is
# at least 3 s after it, and a loaded host has been seen to take 700 ms to return.  It stays at
# 1500 ms, below SLACK, because it is measured from the cancellation itself: on 2026-11-02, at load
# average up to 1130, no call took more than 250 ms from it.

cancelled='cause="the call was cancelled \(cancel\)"'
first='^((stream |upload )?call|stream) 0 '

if scenario cancel-before; then
  evil cancel-before 18180 || exit 1
  client cancel-before call GET "http://127.0.0.1:18180/ok" cancel=0
  expect cancel-before "call 0 error delivery=not sent .*rounds=0 .*retries=0 not_retried=LeanHttp.Call.NoRetry.cause .*$cancelled detail=\"cancelled before the request was sent\"" \
    "a call whose token was cancelled before it started fails at once, not sent"
  conns cancel-before 0 "and opens no connection"
  trace_ok cancel-before
fi

if scenario cancel-head; then
  evil cancel-head 18181 || exit 1
  # The server answers 5 s after it has the request; the call is cancelled 100 ms after that, with
  # its receive pending.
  client cancel-head call GET "http://127.0.0.1:18181/stall-head?ms=5000" cancel=100 \
    log="$out/cancel-head.evil.log" logtext="GET /stall-head"
  expect cancel-head "call 0 error delivery=maybe delivered .*not_retried=LeanHttp.Call.NoRetry.cause .*$cancelled" \
    "a call waiting for the response head is cancelled, maybe delivered, not retried"
  since_fired cancel-head "$first" 0 1500 "at the cancellation, not when the server answers"
  expect cancel-head '^pool idle=0 checked_out=0 allocated=1$' "its connection is closed, not pooled"
  conns cancel-head 1 "one connection, the request not sent again"
  # The same with a body of bytes still being written to a server that does not read: the write
  # cannot be cancelled and is abandoned.  Cancelled once the server sees the first bytes.
  start cancel-write noread "listening" "$PY" -I "$here/noread.py" 18182 || exit 1
  client cancel-write call POST "http://127.0.0.1:18182/" body=32000000 gap=10000 cancel=100 \
    log="$out/cancel-write.noread.log" logtext="bytes arrived"
  expect cancel-write "call 0 error delivery=maybe delivered .*$cancelled" \
    "a call whose request a peer does not read is cancelled, maybe delivered"
  since_fired cancel-write "$first" 0 1500 "at the cancellation, the pending write abandoned"
  expect cancel-write '^pool idle=0 checked_out=0 allocated=1$' \
    "its connection, with the request written in part, is closed, not pooled"
  # Cancelled in the exchange after a redirect, once the server has the second hop's request.
  client cancel-redirect call GET "http://127.0.0.1:18181/redir/302?to=/stall-head%3Fms%3D5000" cancel=100 \
    log="$out/cancel-head.evil.log" logtext="GET /stall-head"
  # The delivery is the furthest any request of the call got: the redirect was a response.
  expect cancel-redirect "call 0 error delivery=response received .*hops=1 retries=0 not_retried=LeanHttp.Call.NoRetry.cause status=none $cancelled" \
    "a call cancelled at its second hop, after a redirect: response received (the redirect's), no status of its own"
  since_fired cancel-redirect "$first" 0 1500 "at the cancellation"
  for s in cancel-head cancel-write cancel-redirect; do trace_ok $s; done
fi

if scenario cancel-body; then
  evil cancel-body 18183 || exit 1
  # A body of a million bytes, one byte every 5 ms: cancelled while Client.request reads it, 300 ms
  # after the response went to its reader.
  client cancel-body call GET "http://127.0.0.1:18183/trickle?ms=5" cancel=300 after=deliver
  expect cancel-body "call 0 error delivery=response received .*status=\\(some 200\\) .*$cancelled" \
    "a call cancelled while its body is read whole: response received, with the status"
  since_fired cancel-body "$first" 0 1500 "at the cancellation"
  expect cancel-body '^pool idle=0 checked_out=0 allocated=1$' "its connection is closed, not pooled"
  # The same while the callback of withResponse reads it in pulls, 100 ms after its first read.
  client cancel-stream stream GET "http://127.0.0.1:18183/trickle?ms=5" cancel=100 after=read pull=1
  expect cancel-stream "stream call 0 error delivery=response received .*$cancelled.* read_before=[1-9][0-9]*\$" \
    "a callback reading the body when the call is cancelled: the read raises the call's error"
  since_fired cancel-stream "$first" 0 1500 "at the cancellation"
  expect cancel-stream '^after stream 0: pool idle=0 checked_out=0 allocated=1$' "its connection is closed, not pooled"
  # A callback busy with something else when the call is cancelled, 200 ms into its 400 ms: its
  # next read raises.
  client cancel-callback stream GET "http://127.0.0.1:18183/trickle?ms=5" cancel=200 after=idle idle=400 pull=1
  expect cancel-callback "stream call 0 error delivery=response received .*$cancelled.* read_before=0\$" \
    "a callback that reads after the call was cancelled: its first read raises the call's error"
  since_fired cancel-callback "$first" 190 1500 "when the callback read, after the rest of its 400 ms"
  # Bytes the stream already holds are not handed out after the cancellation: a pull of one byte
  # takes a whole read of a large body, the call is cancelled while the callback waits (200 ms into
  # its 400 ms), and its next read raises.
  client cancel-held stream GET "http://127.0.0.1:18183/bigbody?n=10000000" cancel=200 after=hold pull=1 stop=1 hold=400
  expect cancel-held "stream call 0 error delivery=response received .*$cancelled.* read_before=1\$" \
    "a read after the cancellation raises, though the stream holds bytes already read"
  # A callback that returns without reading: its result stands, the connection is not pooled.
  client cancel-return stream GET "http://127.0.0.1:18183/ok" cancel=200 after=idle idle=400 stop=0 repeat=2 cancelcalls=1
  expect cancel-return 'stream 0 ok status=200 read=0 ' "a callback that returns normally after the cancellation: its result is the call's"
  expect cancel-return '^after stream 0: pool idle=0 checked_out=0 allocated=1$' \
    "the connection, whose body was held unread, is closed, not pooled"
  expect cancel-return 'stream 1 ok status=200 read=0 .*conn=\(some 1\) reused=false ' \
    "the next call, not cancelled, opens a fresh connection"
  expect cancel-return '^after stream 1: pool idle=1 checked_out=0 allocated=2$' "and its connection goes back to the pool"
  client cancel-return-control stream GET "http://127.0.0.1:18183/ok" idle=400 stop=0
  expect cancel-return-control '^after stream 0: pool idle=1 checked_out=0 allocated=1$' \
    "control: without the cancellation the same connection goes back to the pool"
  for s in cancel-body cancel-stream cancel-callback cancel-held cancel-return cancel-return-control; do trace_ok $s; done
fi

if scenario cancel-upload; then
  uploads cancel-upload 18184 || exit 1
  # A producer that takes 100 ms per chunk: the call is cancelled while it makes one, 50 ms into
  # its fourth, after which that one takes 5 s more.
  client cancel-upload upload PUT "http://127.0.0.1:18184/sink" size=1000000 chunk=1000 delay=100 \
    cancel=50 after=pull:4 stall=5000
  expect cancel-upload "upload call 0 error delivery=maybe delivered .*$cancelled.* pulls=[1-9] produced=[0-9]+\$" \
    "a streamed upload cancelled while its producer works: maybe delivered, not retried"
  since_fired cancel-upload "$first" 0 1500 "at the cancellation, the producer abandoned"
  expect cancel-upload '^after upload 0: pool idle=0 checked_out=0 allocated=1$' \
    "its connection, with the request written in part, is closed, not pooled"
  trace_ok cancel-upload
fi

if scenario cancel-tls; then
  tls_server cancel-tls 18185 good --mode hang || exit 1
  # Cancelled 100 ms after the server sees the ClientHello, which it never answers.
  client cancel-tls call GET "https://127.0.0.1:18185/hello" ca="$certs/ca.pem" tlshs=5000 cancel=100 \
    log="$out/cancel-tls.tls.log" logtext="the ClientHello arrived"
  expect cancel-tls "call 0 error delivery=not sent .*retries=0 not_retried=LeanHttp.Call.NoRetry.cause .*$cancelled detail=\"cancelled during the TLS handshake\"" \
    "a call cancelled during the TLS handshake: not sent, not retried"
  since_fired cancel-tls "$first" 0 1500 "at the cancellation, its receive cancelled"
  tls_conns cancel-tls 1 "one connection"
  # Over TLS, a call cancelled while its body arrives: the TCP receive under the session is
  # cancelled, and the connection is not pooled.
  tls_server cancel-tls-body 18191 good || exit 1
  # A byte a second, so that the cancellation, 50 ms after the first read, comes while the next is
  # awaited even if its timer is late (once, at load average 480, it had not fired 2.5 s later, by
  # which time the 20 bytes of a byte every 100 ms had all come).
  client cancel-tls-body stream GET "https://127.0.0.1:18191/trickle?ms=1000" ca="$certs/ca.pem" cancel=50 after=read pull=1
  expect cancel-tls-body "stream call 0 error delivery=response received .*$cancelled.* read_before=[1-9][0-9]*\$" \
    "a call over TLS cancelled while its body is read: the read raises the call's error"
  since_fired cancel-tls-body "$first" 0 1500 "at the cancellation"
  expect cancel-tls-body '^after stream 0: pool idle=0 checked_out=0 allocated=1$' "its connection is closed, not pooled"
  for s in cancel-tls cancel-tls-body; do trace_ok $s; done
fi

if scenario cancel-backoff; then
  # Refused at once, then a backoff of 3670 ms (seed 3): cancelled 300 ms into it.
  client cancel-backoff call GET "http://127.0.0.1:$CLOSED/" retries=2 base=4000 cap=4000 seed=3 cancel=300 after=wait
  expect cancel-backoff "call 0 error delivery=not sent .*rounds=1 .*retries=1 not_retried=LeanHttp.Call.NoRetry.cause .*$cancelled detail=\"cancelled while waiting to retry\"" \
    "a call cancelled while it waits to retry fails at once, the retry not sent"
  since_fired cancel-backoff "$first" 0 1500 "at the cancellation, not after the 3670 ms backoff"
  trace_ok cancel-backoff
fi

if scenario cancel-connect; then
  start cancel-connect hole "blackhole" "$PY" -I "$here/blackhole.py" 127.0.0.1 18190 || exit 1
  # Nothing sees a connect attempt hang, so the cancellation is a time: 1 s after the request goes
  # out, ample for the attempt to start, and 4 s before it would time out.
  client cancel-connect call GET "http://127.0.0.1:18190/" connect=5000 cancel=1000 after=send
  expect cancel-connect "call 0 error delivery=not sent .*$cancelled detail=\"cancelled while connecting; could not connect: 127\\.0\\.0\\.1:18190 \\(round 0\\): abandoned\"" \
    "a call cancelled while its connect attempt hangs: not sent, the attempt abandoned"
  since_fired cancel-connect "$first" 0 1500 "at the cancellation"
  trace_ok cancel-connect
fi

if scenario cancel-cap; then
  evil cancel-cap 18187 || exit 1
  # Two calls, one connection allowed: one is in its exchange, the other waits for the connection;
  # one token cancels both, 200 ms after both requests went out and the server has the first.
  client cancel-cap call GET "http://127.0.0.1:18187/sleep?ms=5000" concurrent=2 maxactive=1 cancel=200 \
    after=send:2 log="$out/cancel-cap.evil.log" logtext="GET /sleep"
  expect cancel-cap "call [01] error delivery=maybe delivered .*$cancelled" "the call in its exchange is cancelled"
  expect cancel-cap "call [01] error delivery=not sent .*$cancelled detail=\"cancelled while (waiting for|taking) a connection" \
    "the call waiting at the cap is cancelled, not sent"
  since_fired cancel-cap '^round 0 of 2 calls took' 0 1500 "both return at the cancellation"
  # The token on the waiting call only: the call holding the connection keeps it, so only the
  # cancellation can end the wait.
  client cancel-cap-waiter call GET "http://127.0.0.1:18187/sleep?ms=5000" concurrent=2 maxactive=1 cancel=200 \
    after=send:2 log="$out/cancel-cap.evil.log" logtext="GET /sleep" cancelfrom=1
  expect cancel-cap-waiter 'call 0 ok status=200 ' "the call holding the connection is answered"
  expect cancel-cap-waiter "call 1 error delivery=not sent .*$cancelled detail=\"cancelled while waiting for a connection: the origin is at maxActivePerOrigin\"" \
    "the waiting call alone is cancelled, while it waits"
  since_fired cancel-cap-waiter '^call 1 error' 0 1500 "at the cancellation, not when the connection comes back"
  for s in cancel-cap cancel-cap-waiter; do trace_ok $s; done
fi

if scenario shutdown; then
  evil shutdown 18188 || exit 1
  # Shut down 100 ms after the server has the three requests.
  client shutdown call GET "http://127.0.0.1:18188/sleep?ms=5000" concurrent=3 shutdown=100 \
    log="$out/shutdown.evil.log" logtext="GET /sleep" logcount=3
  got=$(grep --count --extended-regexp '^call [0-2] error delivery=maybe delivered .*cause="the call was cancelled \(shutdown\)"' "$out/shutdown.txt")
  if [ "$got" -eq 3 ]; then
    result PASS shutdown "shutting the client down cancels its three calls in flight"
  else
    result FAIL shutdown "shutting the client down cancelled $got of the three calls in flight"
  fi
  since_fired shutdown '^round 0 of 3 calls took' 0 1500 "they return at the shutdown"
  expect shutdown '^after shutdown: call 3 error delivery=not sent .*cause="the call was cancelled \(shutdown\)"' \
    "a call after the shutdown fails at once"
  expect shutdown '^after shutdown: pool idle=0 checked_out=0$' "no connection is pooled"
  # A call waiting at the active cap: the shutdown closes the pool, which wakes it, and it still
  # reports the shutdown, not the closed pool.
  client shutdown-cap call GET "http://127.0.0.1:18188/sleep?ms=5000" concurrent=2 maxactive=1 shutdown=200 \
    after=send:2 log="$out/shutdown.evil.log" logtext="GET /sleep"
  expect shutdown-cap 'call [01] error delivery=maybe delivered .*cause="the call was cancelled \(shutdown\)"' \
    "the call in its exchange is cancelled by the shutdown"
  expect shutdown-cap 'call [01] error delivery=not sent .*cause="the call was cancelled \(shutdown\)" detail="cancelled while (waiting for|taking) a connection' \
    "the call waiting at the cap is cancelled by the shutdown, not refused by the closed pool"
  since_fired shutdown-cap '^round 0 of 2 calls took' 0 1500 "both return at the shutdown"
  # A call waiting to retry, 300 ms into its wait.
  client shutdown-backoff call GET "http://127.0.0.1:$CLOSED/" retries=2 base=4000 cap=4000 seed=3 shutdown=300 after=wait
  expect shutdown-backoff 'call 0 error delivery=not sent .*retries=1 .*cause="the call was cancelled \(shutdown\)" detail="cancelled while waiting to retry"' \
    "a call waiting to retry is cancelled by the shutdown"
  since_fired shutdown-backoff "$first" 0 1500 "at the shutdown"
  for s in shutdown shutdown-cap shutdown-backoff; do trace_ok $s; done
fi

# Cancelled as a step of the call is taken, in the client's record of the call (Config.observe):
# cancel=0 after=STEP.
if scenario cancel-steps; then
  evil cancel-steps 18193 || exit 1
  client cancel-follow call GET "http://127.0.0.1:18193/chain/1" cancel=0 after=follow
  expect cancel-follow "call 0 error delivery=response received .*hops=1 .*$cancelled detail=\"cancelled before the redirect was followed\"" \
    "cancelled as the planner decides to follow a redirect: the redirect is not followed"
  expect cancel-follow '^pool idle=0 checked_out=0 allocated=1$' "the redirect's connection, its body not drained, is closed"
  if ! grep --quiet 'conn1 req1 GET /chain/1 ' "$out/cancel-steps.evil.log"; then
    result FAIL cancel-follow "the server did not see the first request"
  elif grep --quiet 'GET /chain/0' "$out/cancel-steps.evil.log"; then
    result FAIL cancel-follow "the redirect was followed"
  else
    result PASS cancel-follow "the server never saw the redirect's request"
  fi
  client cancel-wait call GET "http://127.0.0.1:$CLOSED/" retries=2 base=4000 cap=4000 seed=3 cancel=0 after=wait
  expect cancel-wait "call 0 error delivery=not sent .*retries=1 .*$cancelled detail=\"cancelled while waiting to retry\"" \
    "cancelled as the wait before a retry begins: the retry is not sent"
  since_fired cancel-wait "$first" 0 1500 "at once, not after the 3670 ms backoff"
  client cancel-deliver stream GET "http://127.0.0.1:18193/ok" cancel=0 after=deliver
  expect cancel-deliver "stream call 0 error delivery=response received .*$cancelled.* read_before=0\$" \
    "cancelled as the response is handed to the callback: its first read raises"
  expect cancel-deliver '^after stream 0: pool idle=0 checked_out=0 allocated=1$' "its connection is closed, not pooled"
  for s in cancel-follow cancel-wait cancel-deliver; do trace_ok $s; done
fi

# --- A timer of the event loop fires early when the loop's thread is held up (NOTES.md, "Timers fire
# early"); no wait of the client may end before its time.  The client pins the loop's thread to one
# CPU, where busy loops hold it up, while threads of its own use the loop (hammer=); bare timers of
# the loop, which do fire early then, are the control.
if scenario timers; then
  # The last CPU this process may use.
  cpu=$(sed --quiet 's/^Cpus_allowed_list:[[:space:]]*//p' /proc/self/status | tr ',' '\n' | tail --lines=1)
  cpu=${cpu##*-}
  hogs=()
  for _ in $(seq 16); do taskset --cpu-list "$cpu" bash -c 'while :; do :; done' & hogs+=($!); done
  pids+=("${hogs[@]}")
  client timers timers n=10 hammer=4 pinloop="$cpu"
  kill "${hogs[@]}" 2>/dev/null
  wait "${hogs[@]}" 2>/dev/null
  if grep --quiet '^pinloop failed' "$out/timers.txt"; then
    result SKIP timers "$(grep '^pinloop failed' "$out/timers.txt")"
  else
    # The control: how often the client's waits saw a timer fire early and started it again.
    again=0
    for kind in awaitFirst race; do
      line=$(grep "^timers $kind " "$out/timers.txt")
      w=$(sed --quiet 's/.* waits=\([0-9]*\) .*/\1/p' <<< "$line")
      t=$(sed --quiet 's/.* timers=\([0-9]*\).*/\1/p' <<< "$line")
      again=$(( again + ${t:-0} - ${w:-0} ))
    done
    bare=$(sed --quiet 's/^timers sleep .* early_over_1ms=\([0-9]*\) .*/\1/p' "$out/timers.txt")
    if [ "$again" -gt 0 ]; then
      result PASS timers "control: the client's waits saw $again timers fire early and started them again (and ${bare:-?} of 40 bare timers ended more than 1 ms early)"
    else
      result SKIP timers "control: no timer of the client's waits fired early in this run (${bare:-?} of 40 bare timers did), so the checks below had nothing to catch"
    fi
    for kind in awaitFirst race; do
      expect timers "^timers $kind waits=40 early=0 " "no wait through $kind ends before its time"
    done
  fi
fi

# --- The lookups of a call: a name is looked up once per call, whatever its rounds of connect attempts.
if scenario dns-once; then
  client dns-once call GET "http://dup.test:$CLOSED/" retries=2 base=0 cap=0
  expect dns-once 'call 0 error delivery=not sent .*rounds=3 lookups=1 .*retries=2 ' \
    "three rounds of connect attempts to one name, after one lookup"
  evil dns-once-redirect 18189 || exit 1
  client dns-once-redirect call GET "http://dup.test:18189/chain/2" pool=0
  expect dns-once-redirect 'call 0 ok status=200 .*rounds=3 lookups=1 .*hops=2 ' \
    "two redirects to the same name, each on a connection of its own, after one lookup"
  client dns-once-literal call GET "http://127.0.0.1:18189/chain/2" pool=0
  expect dns-once-literal 'call 0 ok status=200 .*rounds=3 lookups=0 .*hops=2 ' "an IP literal is not looked up"
  for s in dns-once dns-once-redirect dns-once-literal; do trace_ok $s; done
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
  within dns-timeout 1990 $((2000 + SLACK)) "at the 2 s deadline"
  # Cancelled while the name is looked up: the call returns at once; the lookup, which cannot be
  # cancelled, is abandoned as the deadline abandons it, and delays exit as before.  Nothing sees the
  # lookup hang, so the cancellation is a time: 1 s after the request goes out.
  printf 'nameserver 127.0.0.1\n' > /etc/resolv.conf || exit 1
  known_exit="the abandoned lookup delays exit until the resolver gives up, and the process often crashes then (NOTES.md)" \
    client dns-cancel call GET "http://slow.test/" deadline=10000 cancel=1000 after=send
  cp /tmp/resolv.conf.saved /etc/resolv.conf
  expect dns-cancel "call 0 error delivery=not sent .*lookups=1 .*$cancelled detail=\"cancelled while the name was looked up\"" \
    "a call cancelled while its name is looked up: not sent"
  since_fired dns-cancel "$first" 0 1500 "at the cancellation"
fi

cleanup
# Every call of every scenario had its steps checked against the planner.
bad=$(grep --files-with-matches 'trace call .* FAIL' "$out"/*.txt 2>/dev/null | xargs --no-run-if-empty --max-args=1 basename | tr '\n' ' ')
if [ -n "$bad" ]; then
  result FAIL traces "calls whose steps the planner does not replay, in: $bad"
else
  result PASS traces "every call's steps replay through the planner ($(cat "$out"/*.txt | grep --count 'trace call .* ok') calls)"
fi
# bash's own errors name the script and line ("run.sh: line N: since: command not found"); its notices
# of a child that died of a signal (dns-cancel's crash at exit) give a process id there instead.
errors=$(grep --extended-regexp 'run\.sh: line [0-9]+: ' "$out/stderr.txt" 2>/dev/null \
  | grep --invert-match --extended-regexp 'run\.sh: line [0-9]+: +[0-9]+ ')
if [ -n "$errors" ]; then
  result FAIL run "the suite itself failed: $(head --lines=1 <<< "$errors")"
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
