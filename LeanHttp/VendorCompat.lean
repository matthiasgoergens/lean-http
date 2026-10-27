module

public import Std.Http.Data

public section

/-!
# Data-layer helpers for the vendored protocol layer

The vendored copy of the upstream HTTP/1.1 protocol layer (`scripts/vendor.sh`) uses two helpers
that the same upstream stack adds to `Std.Http`'s data layer and that v4.34.1 lacks.  They are
copied here from that stack (leanprover/lean4 PR 14548 at 3e6f42a58a955f7fd9a6df4213f3be4bb68e3e3b)
under the names the protocol layer expects.  If a toolchain ships them, these declarations clash
with it, and both they and the vendored copy should go.
-/

namespace Std.Http

set_option linter.all true

namespace Status

/--
Checks if the status code is an *interim* response: one that precedes a final response, so a client
that receives it keeps reading the same exchange.

This is every informational status except `101 Switching Protocols`, which RFC 9110 §15.2.2 makes
the server's last HTTP/1.1 response on the connection: the protocol changes immediately after it,
so no final response follows.
-/
@[inline]
def isInterim (c : Status) : Bool :=
  c.isInformational ∧ c.toCode != 101

end Status

namespace Method

/--
Returns `false` for methods whose semantics do not anticipate request content, the ones RFC 9110
§8.6 tells a user agent not to send a `Content-Length` for when the request carries none.
-/
def anticipatesContent (m : Method) : Bool :=
  !(m == .get || m == .head || m == .delete || m == .options || m == .trace || m == .connect)

end Method

end Std.Http
