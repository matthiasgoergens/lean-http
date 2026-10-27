module

public import Std.Net.Addr
public import Std.Http.Data.URI

public section

/-!
# Addresses

Which addresses a call connects to, and in what order.  A host that is an IP literal (IPv6 ones
included) is used as it is, without name resolution.  Answers from name resolution are
de-duplicated, keeping the first occurrence of each (`getaddrinfo` without a socket type returns
every address once per socket type), and then interleaved by family, starting with the family of the
first answer, as RFC 8305 §4 does.
-/

namespace LeanHttp

set_option linter.all true

open Std.Net Std.Http

/--
Where a call connects to: an address given literally, or a name to resolve.
-/
inductive Target where
  /--
  An IP literal from the URI, used without name resolution.
  -/
  | literal (addr : IPAddr)

  /--
  A host name, to be resolved.
  -/
  | name (host : String)
deriving Inhabited, BEq

namespace Target

/--
The target for the host of a URI.  IPv4 and IPv6 literals (the latter written in brackets in the
URI, and stored without them) bypass name resolution.
-/
def ofHost : URI.Host → Target
  | .ipv4 addr => .literal (.v4 addr)
  | .ipv6 addr => .literal (.v6 addr)
  | .name host => .name host.val

end Target

namespace Address

/--
Removes repeated elements, keeping the first occurrence of each, in order.
-/
def dedup {α : Type} [BEq α] (xs : Array α) : Array α :=
  xs.foldl (init := #[]) fun acc x => if acc.contains x then acc else acc.push x

/--
Alternates `xs` and `ys`, starting with `xs`; whatever is left of the longer one follows.
-/
def alternate {α : Type} (xs ys : List α) : List α :=
  match xs, ys with
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => x :: y :: alternate xs ys

/--
Interleaves the address families, starting with the family of the first address and keeping the
order within each family.
-/
def interleave (addrs : Array IPAddr) : Array IPAddr :=
  match addrs[0]? with
  | none => #[]
  | some first =>
    let (same, other) := addrs.toList.partition (·.family == first.family)
    (alternate same other).toArray

/--
The order in which to try the answers of name resolution: de-duplicated, then interleaved by family.
-/
def connectOrder (addrs : Array IPAddr) : Array IPAddr :=
  interleave (dedup addrs)

/--
The socket address for an IP address and a port.
-/
def withPort (addr : IPAddr) (port : UInt16) : SocketAddress :=
  match addr with
  | .v4 addr => .v4 { addr, port }
  | .v6 addr => .v6 { addr, port }

end Address

end LeanHttp
