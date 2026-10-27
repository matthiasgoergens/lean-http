#!/usr/bin/env bash
# Repeats the dns-timeout scenario to see how the process exits after a call that gave up on a name
# lookup: inside the container of scripts/remote.sh, with the resolver pointed at a name server that
# never answers.  From the repository root:
#
#   scripts/remote.sh bash tests/net/dns-exit.sh [runs]
cd /w/tests/net || exit 1
cp /etc/resolv.conf /tmp/resolv.conf.saved 2>/dev/null
printf 'nameserver 127.0.0.1\n' > /etc/resolv.conf || exit 1
/py/bin/python3 -I dnsblack.py > /tmp/dns.log 2>&1 &
server=$!
trap 'kill $server; cp /tmp/resolv.conf.saved /etc/resolv.conf 2>/dev/null' EXIT
sleep 0.5
for i in $(seq "${1:-10}"); do
  t0=$(date +%s%N)
  timeout 60 /w/.lake/build/bin/net-client call GET http://slow.test/ deadline=2000 > /tmp/o.txt 2>&1
  rc=$?
  t1=$(date +%s%N)
  echo "run $i: exit status $rc, wall $(( (t1 - t0) / 1000000 )) ms; $(grep '^call 0' /tmp/o.txt | cut --characters=1-80); $(grep '^main returning' /tmp/o.txt)"
done
