import Lake
open Lake DSL

package «lean-http»

/--
The upstream HTTP/1.1 protocol layer, renamed to `LeanHttpProto.Http.Protocol`.  Generated into
`vendor/` by `scripts/vendor.sh`, which must run before the first build; see NOTES.md.
-/
lean_lib LeanHttpProto where
  srcDir := "vendor"
  roots := #[`LeanHttpProto.Http.Protocol.H1]

@[default_target]
lean_lib LeanHttp where
  leanOptions := #[⟨`autoImplicit, false⟩]
  -- The proofs about the exchange core and the codec are checked by every build, but no other module
  -- imports them.
  roots := #[`LeanHttp, `LeanHttp.Codec, `LeanHttp.Codec.Proofs, `LeanHttp.Exchange.Proofs,
    `LeanHttp.Exchange.Liveness]

/-- Helpers shared by the test executables. -/
lean_lib TestSupport where
  globs := #[.submodules `Tests.Support]

/-- Drives the HTTP/1.1 machine as a client over recorded response shapes. -/
lean_exe «codec-tests» where
  root := `Tests.Codec

/-- Runs the response codec over the same response shapes. -/
lean_exe «response-codec-tests» where
  root := `Tests.ResponseCodec

/-- Differential test of the response codec against the vendored machine. -/
lean_exe «codec-diff» where
  root := `Tests.CodecDiff

/-- Times the response codec and the vendored machine on large bodies. -/
lean_exe «codec-bench» where
  root := `Tests.CodecBench

/-- Pure unit tests: backoff schedule, address ordering, error classification. -/
lean_exe «unit-tests» where
  root := `Tests.Unit

/-- Executable verification of the exchange core: traces, random properties, exploration. -/
lean_exe «core-tests» where
  root := `Tests.Core

/-- Real-socket test driver, run by `tests/net/run.sh` against local servers. -/
lean_exe «net-client» where
  root := `Tests.Net
