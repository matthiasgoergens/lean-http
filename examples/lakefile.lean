import Lake
open Lake DSL

/-!
The examples of README.md, as a package of their own that depends on lean-http the way any user's
package does (by path here, by Git in a real project).  It takes the toolchain from the
`lean-toolchain` of the directory above.  `examples/run.sh` builds them and runs them against
`examples/server.py`.
-/

package «lean-http-examples»

require «lean-http» from ".."

@[default_target]
lean_exe «request-example» where
  root := `RequestExample

@[default_target]
lean_exe «stream-example» where
  root := `StreamExample
