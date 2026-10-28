#!/usr/bin/env bash
# Compiles the fuzzing harness with AFL++ instrumentation: the C that `lake build Fuzz` generated
# for the harness, the checker's step properties, the exchange core and its codec, and the oracle
# (the former core and the vendored protocol layer), plus fuzz/afl-main.c, linked against the Lean
# toolchain's runtime and standard library (which stay uninstrumented).
#
# Runs inside the AFL++ image (fuzz/run.sh), in the tree, after `lake build Fuzz` ran in the Lean
# image.  Writes .lake/fuzz/<variant>/lean-http-fuzz, where the variant is
#   plain    instrumented for coverage (afl-clang-fast, PCGUARD);
#   cmplog   instrumented for AFL++'s comparison logging (afl-fuzz -c).
#
# Usage: fuzz/build.sh [variant...]   (default: plain cmplog)
T=${LEAN_TOOLCHAIN:-/root/.elan/toolchains/leanprover--lean4---v4.34.1}
ir=.lake/build/ir
srcs=("$ir/Fuzz/Harness.c" "$ir/Tests/Support/Check.c" "$ir/LeanHttp/Exchange.c" "$ir/LeanHttp/Error.c"
      "$ir"/LeanHttp/Codec/{Basic,Lines,Fields,Head,Chunked,Response,Request}.c
      "$ir/Tests/Support/MachineCore.c"
      "$ir/LeanHttp/VendorCompat.c" "$ir/LeanHttpProto/Http/Protocol/H1.c"
      "$ir"/LeanHttpProto/Http/Protocol/H1/*.c)
for s in "${srcs[@]}"; do
  [ -f "$s" ] || { echo "build.sh: $s is missing; run lake build Fuzz first" >&2; exit 1; }
done
cflags=(-O2 -g -I "$T/include" -fno-strict-aliasing -ffp-contract=off -fvisibility=hidden -w)
# leanc --print-ldflags, without Lake (not needed) and with the toolchain's own libgmp, libuv,
# OpenSSL and libc++ (in $T/lib).
ldflags=(-L "$T/lib/lean" -L "$T/lib"
         -Wl,--start-group -lleancpp -lLean -Wl,--end-group -lStd
         -Wl,--start-group -lInit -lleanrt -Wl,--end-group
         -Wl,-Bstatic -lc++ -lc++abi -lunwind -lgmp -luv -lssl -lcrypto -Wl,-Bdynamic
         -lpthread -ldl -lrt -Wl,--gc-sections -lm)

variants=("$@")
[ ${#variants[@]} -gt 0 ] || variants=(plain cmplog)
for v in "${variants[@]}"; do
  out=.lake/fuzz/$v
  rm --recursive --force "$out" || exit 1
  mkdir --parents "$out/obj" || exit 1
  envs=()
  case $v in
    plain) ;;
    cmplog) envs=(AFL_LLVM_CMPLOG=1) ;;
    *) echo "build.sh: unknown variant $v" >&2; exit 1 ;;
  esac
  objs=()
  for s in "${srcs[@]}" fuzz/afl-main.c; do
    o=$out/obj/$(echo "${s#"$ir"/}" | tr / _).o
    env "${envs[@]}" AFL_QUIET=1 afl-clang-fast "${cflags[@]}" -c "$s" -o "$o" || exit 1
    objs+=("$o")
  done
  env "${envs[@]}" AFL_QUIET=1 afl-clang-fast -o "$out/lean-http-fuzz" "${objs[@]}" "${ldflags[@]}" || exit 1
  echo "built $out/lean-http-fuzz"
done
