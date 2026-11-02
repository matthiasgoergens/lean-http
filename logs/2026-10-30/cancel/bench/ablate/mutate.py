import sys
from pathlib import Path
M = {
 "all": [],
 "notrack": [("LeanHttp/Client.lean", "  track client number (some watch)\n", ""),
             ("LeanHttp/Client.lean", "    track client number none\n", "")],
 "nocheck": [("LeanHttp/Cancel.lean", "  for token in c.tokens do\n    if let some reason ← token.getCancellationReason then return some reason\n", "")],
 "nonext": [("LeanHttp/Body.lean", "  match ← live.cancel.reason? with\n  | some reason =>\n    let (ex, actions) := live.ex.step (← IO.monoMsNow) (.cancel reason)\n    return ({ live with ex }, actions)\n  | none => pure ()\n", "")],
 "nohook": [("LeanHttp/Body.lean", "  cancel.onCancel do\n    mailbox.inbox.modify (·.push (cancelOp, .cancelled))\n    (← mailbox.bell.get).resolve ()\n", "")],
}
if sys.argv[1] == "all":
    M["all"] = M["notrack"] + M["nocheck"] + M["nonext"] + M["nohook"]
for f, old, new in M[sys.argv[1]]:
    p = Path(f); s = p.read_text()
    assert s.count(old) == 1, (sys.argv[1], f)
    p.write_text(s.replace(old, new))
