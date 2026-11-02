#!/usr/bin/env bash
# Builds net-client, cost-bench (CostBench.lean) and, where there is a Cancel, cost-scale
# (CostScale.lean) of each <name>:<rev> on the build host through scripts/remote.sh, each in a
# directory of its own (~/lean-http-cost-<name>, from `git archive <rev>` with the generated vendor/
# and this commit's remote.sh), and copies the binaries to ~/lean-http-cost/out/bench/, as
# net-client-<name> and cost-bench-<name>.
# Prints the toolchain, each rev's full hash and each binary's SHA-256.
# Usage: build.sh <name>:<rev> ...   (from anywhere; the repository is this file's)
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
host=$(head -n 1 "$root/.build-host")
[ -d "$root/vendor" ] || { echo "run scripts/vendor.sh first" >&2; exit 1; }
ssh "$host" "mkdir -p ~/lean-http-cost/out/bench" || exit 1
for pair in "$@"; do
  name=${pair%%:*} rev=${pair#*:}
  tree=$(mktemp --directory)
  git -C "$root" archive "$rev" | tar --extract --directory "$tree" || exit 1
  cp -r "$root/vendor" "$tree/vendor" && cp "$root/scripts/remote.sh" "$tree/scripts/remote.sh" || exit 1
  # The interleaved driver (CostBench.lean), as an executable of its own; given a token where the
  # client takes one.
  cp "$here/CostBench.lean" "$tree/CostBench.lean" || exit 1
  printf '\nlean_exe «cost-bench» where\n  root := `CostBench\n' >> "$tree/lakefile.lean"
  if grep --quiet 'cancel : Option Std.CancellationToken := none) : Async (Except Error (Response ByteArray))' "$tree/LeanHttp/Client.lean"; then
    sed --in-place 's/^    (client.request req).block -- CALL$/    (if withToken then client.request req (cancel := some token) else client.request req).block/' "$tree/CostBench.lean"
    grep --quiet 'cancel := some token' "$tree/CostBench.lean" || exit 1
  fi
  # The scaling driver (CostScale.lean), where there is a Cancel to drive.
  targets="net-client cost-bench"
  if [ -f "$tree/LeanHttp/Cancel.lean" ]; then
    cp "$here/CostScale.lean" "$tree/CostScale.lean" || exit 1
    printf '\nlean_exe «cost-scale» where\n  root := `CostScale\n' >> "$tree/lakefile.lean"
    if grep --quiet '(registry : TokenRegistry) : BaseIO Cancel' "$tree/LeanHttp/Cancel.lean"; then
      sed --in-place 's/^  Cancel.watch #\[token\] #\[token\] -- WATCH$/  do Cancel.watch #[token] (← IO.mkRef none) registry/; s/^\/-- The watch of a call given/deriving instance Nonempty for TokenRegistry\n\ninitialize registry : TokenRegistry ← TokenRegistry.new\n\n\/-- The watch of a call given/' "$tree/CostScale.lean"
    elif grep --quiet '^def watch (tokens : Array Std.CancellationToken)$' "$tree/LeanHttp/Cancel.lean"; then
      sed --in-place 's/^  Cancel.watch #\[token\] #\[token\] -- WATCH$/  do Cancel.watch #[token] (← IO.mkRef none)/' "$tree/CostScale.lean"
    elif grep --quiet '(stop : IO.Ref (Option Std.CancellationReason))' "$tree/LeanHttp/Cancel.lean"; then
      sed --in-place 's/^  Cancel.watch #\[token\] #\[token\] -- WATCH$/  do Cancel.watch #[token] #[token] (← IO.mkRef none)/' "$tree/CostScale.lean"
    fi
    # Where the client counts the calls on each token (Cancel.countEnd), as the client does it.
    if grep --quiet '^def countEnd' "$tree/LeanHttp/Cancel.lean"; then
      sed --in-place 's/^  watchOf token -- START$/  do let c ← watchOf token; counts.atomically (m := BaseIO) (modify c.countStart); return c/; s/^  c.finish -- END$/  do let sweeps ← counts.atomically (m := BaseIO) (modifyGet c.countEnd); c.finish sweeps/; s/^\/-- Starts a call.s cancellation/initialize counts : Std.Mutex Cancel.TokenCounts ← Std.Mutex.new {}\n\n\/-- Starts a call'"'"'s cancellation/' "$tree/CostScale.lean"
    fi
    targets="$targets cost-scale"
  fi
  echo "### $name = $(git -C "$root" rev-parse "$rev")"
  LEAN_HTTP_HOST=$host LEAN_HTTP_REMOTE_DIR=lean-http-cost-$name bash "$tree/scripts/remote.sh" \
    bash -c "set -o pipefail; lean --version && lake build $targets 2>&1 | tail -n 2" || exit 1
  rm --recursive --force "$tree"
  ssh "$host" "cd ~/lean-http-cost-$name/.lake/build/bin && cp net-client ~/lean-http-cost/out/bench/net-client-$name && cp cost-bench ~/lean-http-cost/out/bench/cost-bench-$name && if [ -f cost-scale ]; then cp cost-scale ~/lean-http-cost/out/bench/cost-scale-$name; fi && cd ~/lean-http-cost/out/bench && sha256sum net-client-$name cost-bench-$name \$(ls cost-scale-$name 2>/dev/null)" || exit 1
done
