#!/usr/bin/env bash
# Inside the container (started with --add-host two:127.0.0.1 --add-host two:127.0.0.2), after the
# change: the zero settings now refused, and a zero stagger over a name with two addresses, of which
# only the second has a server.  Five calls per setting.
lake build net-client 2>&1 | tail -n 1
grep two /etc/hosts
/py/bin/python3 -m http.server 18080 --bind 127.0.0.2 > /dev/null 2>&1 &
srv=$!
sleep 1
bin=.lake/build/bin/net-client
for args in "http://127.0.0.2:18080/ connect=0" "http://127.0.0.2:18080/ deadline=0" \
    "http://localhost:18080/ deadline=0" "http://two:18080/" "http://two:18080/ stagger=0"; do
  echo "\$ net-client call GET $args repeat=5"
  # shellcheck disable=SC2086
  timeout 60 $bin call GET $args repeat=5
  echo "exit status $?"
done
kill $srv
