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
  -- The proofs about the exchange core, the codec and the planner are checked by every build, but no other module
  -- imports them.
  roots := #[`LeanHttp, `LeanHttp.Codec, `LeanHttp.Codec.Proofs, `LeanHttp.Exchange.Proofs,
    `LeanHttp.Exchange.Liveness, `LeanHttp.Exchange.Response, `LeanHttp.Call.Proofs]

/-- Helpers shared by the test executables. -/
lean_lib TestSupport where
  globs := #[.submodules `Tests.Support]

/-- Drives the exchange core, and through it the codec, over recorded response shapes. -/
lean_exe «codec-tests» where
  root := `Tests.Codec

/-- Runs the response codec over the same response shapes. -/
lean_exe «response-codec-tests» where
  root := `Tests.ResponseCodec

/-- Differential test of the codec and the exchange core against the vendored machine. -/
lean_exe «codec-diff» where
  root := `Tests.CodecDiff

/-- Times the exchange core, the codec alone and the former core over the machine on large bodies. -/
lean_exe «codec-bench» where
  root := `Tests.CodecBench

/-- Pure unit tests: backoff schedule, address ordering, error classification. -/
lean_exe «unit-tests» where
  root := `Tests.Unit

/-- Executable verification of the exchange core: traces, random properties, exploration. -/
lean_exe «core-tests» where
  root := `Tests.Core

/-- Unit tests of the per-call planner, random runs checked step by step, and planted bugs. -/
lean_exe «call-tests» where
  root := `Tests.Call

/-- Differential test of the planner's redirect decisions against the vendored and toolchain planners. -/
lean_exe «call-diff» where
  root := `Tests.CallDiff

/-- Real-socket test driver, run by `tests/net/run.sh` against local servers. -/
lean_exe «net-client» where
  root := `Tests.Net

/-- The fuzzing harness: invariants over one exchange, exported to C for AFL++ (`fuzz/`). -/
lean_lib Fuzz where
  roots := #[`Fuzz.Harness]

/-- Replays fuzz inputs through the harness and prints what happened. -/
lean_exe «fuzz-replay» where
  root := `Fuzz.Replay
