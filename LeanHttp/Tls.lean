module

public import Std.Http.Data.URI

public section

/-!
# TLS: the binding to OpenSSL, the trust store and the server's name

`native/tls.c` drives the toolchain's static OpenSSL over memory BIOs: a `Session` is fed the
ciphertext its TCP socket received and gives the ciphertext to send, and every call returns at once.
`LeanHttp.Transport` does the socket work.  This module holds the bindings, which only declare the C
functions, and the two decisions made before a session exists, both pure enough to test:

- **which certificates to trust** (`chooseTrust`): `Config.tls.caFile` if given; else
  `SSL_CERT_FILE` and `SSL_CERT_DIR`, as OpenSSL honours them; else the first bundle file of
  `wellKnownFiles` that exists, and only then the directories of `wellKnownDirs` that hold OpenSSL's
  hashed names.  Never OpenSSL's compiled-in default, which in the toolchain's OpenSSL is a Nix store
  path.
- **the name the certificate must carry** (`serverName`): a host name (also sent as SNI) or an IP
  address (no SNI, which RFC 6066 section 3 forbids for literals).
-/

namespace LeanHttp.Tls

set_option linter.all true

open Std.Http

/-- The type behind `Context`. -/
opaque ContextPointed : NonemptyType

/--
An OpenSSL client context with its trust store loaded: TLS 1.2 at least, verification on.  Shared
by every connection of a client.
-/
def Context : Type := ContextPointed.type

instance : Nonempty Context := ContextPointed.property

/-- The type behind `Session`. -/
opaque SessionPointed : NonemptyType

/--
One TLS connection's state in OpenSSL, over memory BIOs.  Driven by one task at a time.
-/
def Session : Type := SessionPointed.type

instance : Nonempty Session := SessionPointed.property

/--
A context trusting the certificates of `caFile` (unless empty) and of each directory of `caDirs`
(OpenSSL's hashed names).  Fails, with a message, if OpenSSL is not version 3 or nothing loads.
-/
@[extern "lean_http_tls_ctx_new"]
opaque Context.create (caFile : @& String) (caDirs : @& Array String) : IO Context

/--
A session for the server `host`: a host name when `isIp` is 0 (sent as SNI, and the certificate's
DNS names must match it), an IP address without brackets otherwise (the certificate must carry it).
-/
@[extern "lean_http_tls_session_new"]
opaque Session.create (ctx : @& Context) (host : @& String) (isIp : UInt8) : IO Session

/-- Advances the handshake; see `Session.handshake`. -/
@[extern "lean_http_tls_handshake"]
opaque Session.handshakeCode (s : @& Session) : IO UInt32

/-- Hands the session ciphertext the socket received. -/
@[extern "lean_http_tls_feed"]
opaque Session.feed (s : @& Session) (bytes : @& ByteArray) : IO Unit

/-- Tells the session that the socket's input has ended. -/
@[extern "lean_http_tls_feed_eof"]
opaque Session.feedEof (s : @& Session) : IO Unit

/-- Takes the ciphertext the session produced, in order, to be sent. -/
@[extern "lean_http_tls_take_output"]
opaque Session.takeOutput (s : @& Session) : IO ByteArray

/-- Encrypts `bytes`; the ciphertext is taken with `takeOutput`.  Throws if the session failed. -/
@[extern "lean_http_tls_write"]
opaque Session.write (s : @& Session) (bytes : @& ByteArray) : IO Unit

/-- Decrypts what the input fed so far holds; see `Session.read`. -/
@[extern "lean_http_tls_read"]
opaque Session.readCode (s : @& Session) (max : USize) : IO (UInt32 × ByteArray)

/--
Whether the session holds nothing (no plaintext or ciphertext buffered, no `close_notify`, no end
of input, no failure), after a complete handshake: only then may its connection be reused.
-/
@[extern "lean_http_tls_clean"]
opaque Session.clean (s : @& Session) : IO Bool

/-- Marks the session failed, so that it is never reused: a read was given up with bytes unread. -/
@[extern "lean_http_tls_poison"]
opaque Session.poison (s : @& Session) : IO Unit

/-- Queues `close_notify`, once, unless the session failed; taken with `takeOutput`. -/
@[extern "lean_http_tls_close_notify"]
opaque Session.closeNotify (s : @& Session) : IO Unit

/-- The message of the session's last failure. -/
@[extern "lean_http_tls_last_error"]
opaque Session.lastError (s : @& Session) : IO String

/-- The protocol version negotiated, such as `TLSv1.3`. -/
@[extern "lean_http_tls_version"]
opaque Session.version (s : @& Session) : IO String

/-- `OPENSSL_VERSION_NUMBER` of the OpenSSL linked in (`0x30600000` for 3.6.0). -/
@[extern "lean_http_tls_openssl_version"]
opaque opensslVersionNumber (u : Unit) : IO UInt64

/--
Where a handshake stands after a step.
-/
inductive HandshakeStep where
  /-- Complete. -/
  | done
  /-- It needs more input from the server. -/
  | wantRead
  /-- The certificate or the name was refused, with OpenSSL's reason. -/
  | verify (detail : String)
  /-- An alert, a protocol failure, or an ALPN protocol other than `http/1.1`. -/
  | failed (detail : String)
  /-- The connection ended during the handshake. -/
  | closed (detail : String)
deriving Repr

/--
Advances the handshake with the input fed so far.  The output it produced is taken with
`takeOutput`.
-/
def Session.handshake (s : Session) : IO HandshakeStep := do
  match ← s.handshakeCode with
  | 0 => return .done
  | 1 => return .wantRead
  | 2 => return .verify (← s.lastError)
  | 4 => return .closed (← s.lastError)
  | _ => return .failed (← s.lastError)

/--
What a read from a session gave.
-/
inductive ReadStep where
  /-- Plaintext, never empty. -/
  | data (bytes : ByteArray)
  /-- Nothing yet: the session needs more input. -/
  | wantRead
  /-- The server's `close_notify`: a clean end of input. -/
  | closed
  /-- The input ended without `close_notify`. -/
  | truncated (detail : String)
  /-- An alert or a protocol failure. -/
  | failed (detail : String)

/--
Decrypts up to `max` bytes (at least one) from every record the input fed so far holds.  An end met
after some plaintext is returned by the next read.  Output the reading produced (a key update's
reply) is taken with `takeOutput`.
-/
def Session.read (s : Session) (max : Nat) : IO ReadStep := do
  let (code, bytes) ← s.readCode (max.min (2 ^ 30)).toUSize
  match code with
  | 0 => return if bytes.isEmpty then .wantRead else .data bytes
  | 1 => return .wantRead
  | 2 => return .closed
  | 3 => return .truncated (← s.lastError)
  | _ => return .failed (← s.lastError)

/-! ## The trust store -/

/--
Bundle files of trusted certificates, in the order they are looked for: the list Go's
`crypto/x509` probes on Linux (Debian, Ubuntu and Gentoo; Fedora and RHEL 6; openSUSE; OpenELEC;
CentOS and RHEL 7; Alpine), which also finds macOS's `/etc/ssl/cert.pem`.
-/
def wellKnownFiles : List String :=
  ["/etc/ssl/certs/ca-certificates.crt", "/etc/pki/tls/certs/ca-bundle.crt", "/etc/ssl/ca-bundle.pem",
    "/etc/pki/tls/cacert.pem", "/etc/pki/ca-trust/extracted/pem/tls-ca-bundle.pem", "/etc/ssl/cert.pem"]

/--
Directories of trusted certificates, used only when no bundle file exists, and only if they hold
OpenSSL's hashed names (`5ad8a5d6.0`), which is how OpenSSL looks certificates up in a directory.
-/
def wellKnownDirs : List String :=
  ["/etc/ssl/certs", "/etc/pki/tls/certs"]

/--
What a context is to trust: a bundle file, or none, and directories.
-/
structure Trust where
  /-- A PEM bundle, or `""` for none. -/
  file : String := ""
  /-- Directories with OpenSSL's hashed names. -/
  dirs : Array String := #[]
deriving Repr, BEq

/--
What `chooseTrust` needs to know about the machine.
-/
structure TrustProbe where
  /-- `Config.tls.caFile`. -/
  caFile : Option String := none
  /-- The value of `SSL_CERT_FILE`, if set. -/
  envFile : Option String := none
  /-- The value of `SSL_CERT_DIR`, if set. -/
  envDir : Option String := none
  /-- Whether a file exists at this path. -/
  isFile : String → Bool := fun _ => false
  /-- Whether a directory that can be read exists at this path. -/
  isDir : String → Bool := fun _ => false
  /-- Whether a directory holds at least one of OpenSSL's hashed names. -/
  hasHashed : String → Bool := fun _ => false

/--
Decides what to trust (see the module comment).  An empty variable counts as unset; a variable that
is set but names nothing that exists is an error, not a reason to look elsewhere.  The error says
what to set.
-/
def chooseTrust (p : TrustProbe) : Except String Trust := do
  if let some file := p.caFile then
    return { file }
  let envFile := p.envFile.filter (!·.isEmpty)
  let envDirs := (p.envDir.getD "").splitOn ":" |>.filter (!·.isEmpty)
  if let some d := p.envDir then
    if !d.isEmpty && envDirs.isEmpty then throw s!"SSL_CERT_DIR is {d.quote}, which names no directory"
  if envFile.isSome || !envDirs.isEmpty then
    if let some f := envFile then
      unless p.isFile f do throw s!"SSL_CERT_FILE names {f}, which is not a file"
    for d in envDirs do
      unless p.isDir d do throw s!"SSL_CERT_DIR names {d}, which is not a directory that can be read"
    return { file := envFile.getD "", dirs := envDirs.toArray }
  if let some f := wellKnownFiles.find? p.isFile then
    return { file := f }
  let dirs := wellKnownDirs.filter fun d => p.isDir d && p.hasHashed d
  if !dirs.isEmpty then
    return { dirs := dirs.toArray }
  throw ("no trusted certificates found: none of " ++ String.intercalate ", " wellKnownFiles ++
    " exists; install the system's CA certificates (ca-certificates), or set Config.tls.caFile, " ++
    "SSL_CERT_FILE or SSL_CERT_DIR")

/--
Whether `name` is one of OpenSSL's hashed names for a certificate: eight hexadecimal digits, a dot
and a number (`5ad8a5d6.0`).
-/
def isHashedName (name : String) : Bool :=
  match name.splitOn "." with
  | [hash, n] =>
    hash.length == 8 && hash.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) &&
      !n.isEmpty && n.all Char.isDigit
  | _ => false

/--
`chooseTrust` on this machine: reads `SSL_CERT_FILE` and `SSL_CERT_DIR` and looks at the file
system, as far as the choice needs: the well-known directories are listed only if no well-known
bundle file exists.  A directory counts only if it can be read.
-/
def discoverTrust (caFile : Option System.FilePath) : IO (Except String Trust) := do
  let envFile ← IO.getEnv "SSL_CERT_FILE"
  let envDir ← IO.getEnv "SSL_CERT_DIR"
  let isFile (f : String) : IO Bool := do
    let path := System.FilePath.mk f
    return !f.isEmpty && (← path.pathExists) && !(← path.isDir)
  -- A readable directory's entries, or `none`.
  let listing (d : String) : IO (Option (Array IO.FS.DirEntry)) := do
    if !(← (System.FilePath.mk d).isDir) then return none
    match ← (System.FilePath.mk d).readDir.toBaseIO with
    | .ok entries => return some entries
    | .error _ => return none
  let mut files : List String := []
  for f in envFile.toList ++ wellKnownFiles do
    if ← isFile f then files := f :: files
  let envDirs := (envDir.getD "").splitOn ":" |>.filter (!·.isEmpty)
  let probeWellKnown := caFile.isNone && !wellKnownFiles.any (files.contains ·)
  let mut dirs : List String := []
  let mut hashed : List String := []
  for d in envDirs ++ (if probeWellKnown then wellKnownDirs else []) do
    if let some entries ← listing d then
      dirs := d :: dirs
      if entries.any (isHashedName ·.fileName) then hashed := d :: hashed
  return chooseTrust {
    caFile := caFile.map (·.toString), envFile, envDir,
    isFile := (files.contains ·), isDir := (dirs.contains ·), hasHashed := (hashed.contains ·) }

/-! ## The server's name -/

/--
The name a server's certificate must carry.
-/
inductive ServerName where
  /-- A host name: the certificate's DNS names must match it, and SNI carries it. -/
  | host (name : String)
  /-- An IP address, without brackets: the certificate must carry it; no SNI. -/
  | ip (address : String)
deriving Repr, BEq

/--
Whether `name` ends in a number, in the WHATWG URL standard's sense: its last label is decimal
digits, or `0x` and hexadecimal digits.  Such a name is no DNS name (no top-level domain is
numeric), and resolvers read it as an IPv4 address: `1.2.3` as 1.2.0.3, `0x7f000001` as 127.0.0.1.
-/
def endsInNumber (name : String) : Bool :=
  let last := (name.splitOn ".").getLast?.getD ""
  let hex := last.startsWith "0x" || last.startsWith "0X"
  let digits := if hex then (last.drop 2).toString else last
  if hex then digits.all Char.isHexDigit
  else !digits.isEmpty && digits.all Char.isDigit

/--
The name `host` must be verified against.  `Std.Http`'s URI parser gives host names as validated,
lowercase ASCII labels, none of them empty, so a name here has no trailing dot, no NUL byte and is
never empty (`SSL_set1_host` with an empty name would turn the name check off; `native/tls.c`
refuses one as well).  A name that ends in a number (`endsInNumber`) is refused: the resolver
would read it as an IPv4 address, and it would be checked as a DNS name and sent as SNI.
-/
def serverName : URI.Host → Except String ServerName
  | .ipv4 addr => .ok (.ip (toString addr))
  | .ipv6 addr => .ok (.ip (toString addr))
  | .name n =>
    let s : String := n
    if s.isEmpty then .error "the host name is empty"
    else if endsInNumber s then
      .error s!"the host name {s.quote} reads as an IPv4 address: write the address in full, a.b.c.d"
    else .ok (.host s)

end LeanHttp.Tls
