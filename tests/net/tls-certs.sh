#!/usr/bin/env bash
# Makes the certificates the TLS scenarios use, at test time (none is committed), with the openssl
# command-line tool, into <dir>:
#
#   ca.pem, ca.key          the test CA, which the client is given (ca=<dir>/ca.pem)
#   good.pem, good.key      a server certificate from it for localhost, 127.0.0.1 and ::1
#   wrong.pem, wrong.key    one from it for other.example only
#   expired.pem, expired.key  one from it for localhost and 127.0.0.1 that expired in 2020
#   rogue-ca.pem            another CA, which the client does not trust
#   untrusted.pem, untrusted.key  a certificate from it for localhost and 127.0.0.1
#   cn-only.pem, cn-only.key  one from the test CA naming localhost only in its common name
#   partial-wild.pem, partial-wild.key  one for w*.lh.test, a partial wildcard
#   full-wild.pem, full-wild.key  one for *.lh.test
#
# Usage: tests/net/tls-certs.sh <dir>
dir=${1:?usage: tls-certs.sh <dir>}
mkdir --parents "$dir" || exit 1
cd "$dir" || exit 1
rm --force ./*.pem ./*.key ./*.csr ./*.ext ./*.srl index.txt* serial* ./*.cnf || exit 1

key() { openssl genpkey -algorithm EC -pkeyopt ec_paramgen_curve:P-256 -out "$1" 2>/dev/null; }

ca() { # ca <name> <common name>
  key "$1.key" || return 1
  openssl req -x509 -new -key "$1.key" -out "$1.pem" -days 2 -subj "/CN=$2" \
    -addext "basicConstraints=critical,CA:TRUE" -addext "keyUsage=critical,keyCertSign,cRLSign"
}

leaf() { # leaf <name> <ca> <subjectAltName>
  key "$1.key" || return 1
  openssl req -new -key "$1.key" -out "$1.csr" -subj "/CN=lean-http test $1" || return 1
  printf 'subjectAltName=%s\nbasicConstraints=CA:FALSE\nextendedKeyUsage=serverAuth\nkeyUsage=digitalSignature\n' \
    "$3" > "$1.ext"
  openssl x509 -req -in "$1.csr" -CA "$2.pem" -CAkey "$2.key" -CAcreateserial -out "$1.pem" -days 2 \
    -extfile "$1.ext" 2>/dev/null
}

ca ca "lean-http test CA" || exit 1
ca rogue-ca "lean-http rogue CA" || exit 1
leaf good ca "DNS:localhost,IP:127.0.0.1,IP:::1" || exit 1
leaf wrong ca "DNS:other.example" || exit 1
leaf untrusted rogue-ca "DNS:localhost,IP:127.0.0.1" || exit 1
leaf partial-wild ca "DNS:w*.lh.test" || exit 1
leaf full-wild ca "DNS:*.lh.test" || exit 1
# A certificate with no subjectAltName, naming localhost only in its common name.
key cn-only.key || exit 1
openssl req -new -key cn-only.key -out cn-only.csr -subj "/CN=localhost" || exit 1
printf 'basicConstraints=CA:FALSE\nextendedKeyUsage=serverAuth\n' > cn-only.ext
openssl x509 -req -in cn-only.csr -CA ca.pem -CAkey ca.key -CAcreateserial -out cn-only.pem -days 2 \
  -extfile cn-only.ext 2>/dev/null || exit 1

# The expired certificate needs a validity in the past, which `openssl ca` can set.
key expired.key || exit 1
openssl req -new -key expired.key -out expired.csr -subj "/CN=lean-http test expired" || exit 1
: > index.txt
echo 1000 > serial
cat > ca.cnf <<'EOF'
[ca]
default_ca = test
[test]
database = index.txt
serial = serial
new_certs_dir = .
default_md = sha256
policy = any
x509_extensions = leaf
unique_subject = no
[any]
commonName = supplied
[leaf]
subjectAltName = DNS:localhost,IP:127.0.0.1
basicConstraints = CA:FALSE
extendedKeyUsage = serverAuth
EOF
openssl ca -batch -config ca.cnf -keyfile ca.key -cert ca.pem -in expired.csr -out expired.pem \
  -startdate 20200101000000Z -enddate 20200102000000Z -notext 2>/dev/null || exit 1

for c in good wrong untrusted expired cn-only partial-wild full-wild; do
  openssl x509 -in "$c.pem" -noout -subject -ext subjectAltName -dates | tr '\n' ' '
  echo
done
