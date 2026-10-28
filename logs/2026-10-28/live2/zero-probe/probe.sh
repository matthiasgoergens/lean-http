#!/usr/bin/env bash
# Inside the container at the tree's root: what the client does today with a zero connect timeout,
# stagger or deadline, against a local HTTP server on loopback.  Five calls per setting.
lake build net-client 2>&1 | tail -n 1
/py/bin/python3 -m http.server 18080 --bind 127.0.0.1 > /dev/null 2>&1 &
srv=$!
sleep 1
bin=.lake/build/bin/net-client
for args in "http://127.0.0.1:18080/" "http://127.0.0.1:18080/ connect=0" \
    "http://127.0.0.1:18080/ stagger=0" "http://localhost:18080/ stagger=0" \
    "http://127.0.0.1:18080/ deadline=0" "http://localhost:18080/ deadline=0" \
    "http://localhost:18080/ connect=0"; do
  echo "\$ net-client call GET $args repeat=5"
  # shellcheck disable=SC2086
  timeout 60 $bin call GET $args repeat=5
  echo "exit status $?"
done
kill $srv
