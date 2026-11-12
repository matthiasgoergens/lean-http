#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Plants one defect in the tree in the current directory, for the positive controls of the checks
added with cancellation and with the lookups of a call.

Usage: mutate.py <name>; MUTATIONS gives each name's file, the text it replaces and what it breaks."""
import sys
from pathlib import Path

MUTATIONS = {
    # The exchange core ignores a cancel: the exchange goes on.
    "core-cancel-ignored": ("LeanHttp/Exchange.lean",
        "  | .cancel reason => failOrDrop (.cancelled reason)\n",
        "  | .cancel _ => pure ()\n"),
    # A cancel finishes the exchange instead of failing it, reusable if the core would allow it.
    "core-cancel-finishes": ("LeanHttp/Exchange.lean",
        "  | .cancel reason => failOrDrop (.cancelled reason)\n",
        "  | .cancel _ => finishNow true\n"),
    # A cancel fails the exchange with another cause.
    "core-cancel-cause": ("LeanHttp/Exchange.lean",
        "  | .cancel reason => failOrDrop (.cancelled reason)\n",
        "  | .cancel _ => failOrDrop .localClose\n"),
    # The planner may retry a cancelled call.
    "planner-retries-cancelled": ("LeanHttp/Call.lean",
        "  | .tls .timeout => true\n",
        "  | .tls .timeout => true\n  | .cancelled _ => true\n"),
    # The record check accepts any failure in place of a request.
    "trace-any-failure": ("LeanHttp/Call/Trace.lean",
        "      unless (f.cause matches .cancelled _) && f.delivery == .notSent && f.written == 0 do\n",
        "      unless true do\n"),
    # No call registers with the caller's token.
    "shell-no-watch": ("LeanHttp/Cancel.lean",
        "    discard <| start (token.selector.registerFn waiter)\n",
        ""),
    # An exchange does not hear of the cancellation through its mailbox.
    "shell-no-mailbox": ("LeanHttp/Body.lean",
        "  cancel.onCancel do\n    mailbox.inbox.modify (·.push (cancelOp, .cancelled))\n    (← mailbox.bell.get).resolve ()\n",
        ""),
    # Abandoning the body of a cancelled call drains it and may pool the connection.
    "shell-abandon-drains": ("LeanHttp/Body.lean",
        "  let (live, _) ← live.cancelNow?\n  if let some verdict := live.verdict then\n",
        "  if let some verdict := live.verdict then\n"),
    # The sleep before a retry does not end at the cancellation.
    "shell-sleep-uncancellable": ("LeanHttp/Cancel.lean",
        "    | .cancelled reason => return some reason\n",
        "    | .cancelled _ => do Std.Async.sleep (.ofNat (target - now)); c.sleepUntil target\n"),
    # The TLS handshake's receive does not end at the cancellation.
    "shell-handshake-uncancellable": ("LeanHttp/Transport.lean",
        "    match ← cancel.race #[recv] left with\n",
        "    match ← (← Cancel.watch #[] #[]).race #[recv] left with\n"),
    # A round of connect attempts does not end at the cancellation.
    "shell-connect-uncancellable": ("LeanHttp/Connect.lean",
        "    match ← cancel.race #[signalled, ended] waitMs with\n",
        "    match ← (← Cancel.watch #[] #[]).race #[signalled, ended] waitMs with\n"),
    # The wait at the active cap does not end at the cancellation.
    "shell-cap-uncancellable": ("LeanHttp/Client.lean",
        "    match ← (try (some <$> a.cancel.race #[freed.result?] left) catch _ => pure none) with\n",
        "    match ← (try (some <$> (← Cancel.watch #[] #[]).race #[freed.result?] left) catch _ => pure none) with\n"),
    # The shell's checks look at the call's signal alone, which the watch resolves a moment after
    # the token is cancelled, not at the tokens.
    "shell-checks-signal-only": ("LeanHttp/Cancel.lean",
        "  for token in c.tokens do\n    if let some reason ← token.getCancellationReason then return some reason\n",
        ""),
    # A read hands out the bytes the stream holds even after the cancellation.
    "stream-hands-out-held": ("LeanHttp/Body.lean",
        "        if (← live.cancel.reason?).isSome then s.advance live else pure state\n",
        "        pure state\n"),
    # The last wait's bell is kept when the call ends, and what is chained on it with it.
    "cancel-keeps-last-bell": ("LeanHttp/Cancel.lean",
        "  c.bell.set none\n",
        ""),
    # shutdownNow cancels the client's token but does not wake the calls in flight.
    "shutdown-no-table": ("LeanHttp/Client.lean",
        "  calls.forM fun (_, c) => c.cancel .shutdown\n",
        "  discard <| pure calls\n"),
    # Every round of connect attempts looks the name up again.
    "lookup-every-round": ("LeanHttp/Client.lean",
        "    if let some addrs := progress.resolved.lookup host then\n",
        "    if let some addrs := (none : Option (Array IPAddr)) then\n"),
}

name = sys.argv[1]
path, old, new = MUTATIONS[name]
p = Path(path)
s = p.read_text()
if s.count(old) != 1:
    sys.exit(f"{name}: the text to change occurs {s.count(old)} times in {path}")
p.write_text(s.replace(old, new))
print(f"planted {name} in {path}")
