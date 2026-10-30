#!/usr/bin/env bash
# Generates the public headers of the OpenSSL release the Lean toolchain links (3.6.0), for the
# check of native/openssl-min.h (scripts/ci.sh, stage tls-abi).  The library itself needs no
# headers.  Fetches the release tarball, checks it against its SHA-256, and runs OpenSSL's Configure
# and `make build_generated`, which need Perl and a C compiler, into $1 (default:
# vendor/openssl-3.6.0, ignored), leaving <dir>/include.  Does nothing if <dir>/include exists.
#
# Usage: scripts/openssl-headers.sh [dir]
version=3.6.0
sha256=b6a5f44b7eb69e3fa35dbf15524405b44837a481d43d81daddde3ff21fcbb8e9
root=$(cd "$(dirname "$0")/.." && pwd) || exit 1
dir=${1:-$root/.lake/openssl-$version}
if [ -f "$dir/include/openssl/ssl.h" ]; then
  echo "OpenSSL $version headers are in $dir/include"
  exit 0
fi
work=$(mktemp --directory) || exit 1
trap 'rm --recursive --force "$work"' EXIT
url=https://github.com/openssl/openssl/releases/download/openssl-$version/openssl-$version.tar.gz
curl --silent --show-error --fail --location --output "$work/openssl.tar.gz" "$url" || exit 1
echo "$sha256  $work/openssl.tar.gz" | sha256sum --check --quiet || { echo "checksum mismatch for $url" >&2; exit 1; }
tar --extract --gzip --file "$work/openssl.tar.gz" --directory "$work" || exit 1
( cd "$work/openssl-$version" && ./Configure no-shared no-tests > configure.log 2>&1 \
    && make build_generated > make.log 2>&1 ) \
  || { tail --lines=30 "$work/openssl-$version"/*.log >&2; exit 1; }
mkdir --parents "$dir" || exit 1
cp --recursive "$work/openssl-$version/include" "$dir/" || exit 1
echo "generated OpenSSL $version headers into $dir/include"
