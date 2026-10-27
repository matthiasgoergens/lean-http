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

/-- Drives the HTTP/1.1 machine as a client over recorded response shapes. -/
lean_exe «codec-tests» where
  root := `Tests.Codec

/-- Pure unit tests: backoff schedule, address ordering, error classification. -/
lean_exe «unit-tests» where
  root := `Tests.Unit

/-- Real-socket test driver, run by `tests/net/run.sh` against local servers. -/
lean_exe «net-client» where
  root := `Tests.Net
