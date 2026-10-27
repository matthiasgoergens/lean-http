import Lake
open Lake DSL

package «lean-http» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib LeanHttp

/-- Drives the HTTP/1.1 machine as a client over recorded response shapes. -/
lean_exe «codec-tests» where
  root := `Tests.Codec

/-- Pure unit tests: backoff schedule, address ordering, error classification. -/
lean_exe «unit-tests» where
  root := `Tests.Unit

/-- Real-socket test driver, run by `tests/net/run.sh` against local servers. -/
lean_exe «net-client» where
  root := `Tests.Net
