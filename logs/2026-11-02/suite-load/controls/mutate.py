#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Plants one defect in the tree in the current directory, for the positive controls of the checks
changed to hold under load (the exit check, the checks of a time, the early timers).

Usage: mutate.py <name>; MUTATIONS gives each name's edits (file, text, replacement) and what it
breaks."""
import sys
from pathlib import Path

MUTATIONS = {
    # The process takes 5 s to exit after main returns: a task still running then delays the exit.
    "exit-delay": [("Tests/Net.lean",
        "  let now ← IO.monoNanosNow\n  IO.println s!\"main returning at ms=",
        "  discard <| IO.asTask (prio := .dedicated) (IO.sleep 5000)\n"
        "  let now ← IO.monoNanosNow\n  IO.println s!\"main returning at ms=")],
    # The waits trust the timer: one that fires early ends the wait early, as before the fix.
    "timer-early-unfixed": [
        ("LeanHttp/Wait.lean",
         "  | none => if (← IO.monoMsNow) < target then awaitFirstUntil tasks target startTimer else return none\n",
         "  | none => return none\n"),
        ("LeanHttp/Cancel.lean",
         "    if (← IO.monoMsNow) < target then c.raceUntil tasks target startTimer else return .timedOut\n",
         "    return .timedOut\n")],
    # The call's deadline is 4 s later than configured (the checks allow 3 s).
    "deadline-late": [("LeanHttp/Client.lean",
        "  let deadline := started + config.deadlineMs\n",
        "  let deadline := started + config.deadlineMs + 4000\n")],
    # The read and write gaps are 4 s longer than configured.
    "gap-late": [("LeanHttp/Client.lean",
        "gapMs := config.readGapMs, gapMs_pos := hg,",
        "gapMs := config.readGapMs + 4000, gapMs_pos := by omega,")],
    # The TLS handshake's time limit is 4 s longer than configured.
    "handshake-late": [("LeanHttp/Client.lean",
        "  let timeoutAt := (← IO.monoMsNow) + a.client.config.tlsHandshakeTimeoutMs\n",
        "  let timeoutAt := (← IO.monoMsNow) + a.client.config.tlsHandshakeTimeoutMs + 4000\n")],
    # The TLS handshake's time limit is half of what is configured.
    "handshake-early": [("LeanHttp/Client.lean",
        "  let timeoutAt := (← IO.monoMsNow) + a.client.config.tlsHandshakeTimeoutMs\n",
        "  let timeoutAt := (← IO.monoMsNow) + a.client.config.tlsHandshakeTimeoutMs / 2\n")],
    # A connect attempt's time limit is 4 s longer than configured.
    "connect-late": [("LeanHttp/Connect.lean",
        "    let task ← start (run i addrs[i] (min config.connectTimeoutMs left))\n",
        "    let task ← start (run i addrs[i] (min (config.connectTimeoutMs + 4000) left))\n")],
    # The wait before a retry is twice the planner's delay.
    "retry-wait-double": [("LeanHttp/Client.lean",
        "    let endsAt := min (clock.now + delay) spec.deadline\n",
        "    let endsAt := min (clock.now + 2 * delay) spec.deadline\n")],
    # A retry goes out without waiting.
    "retry-wait-none": [("LeanHttp/Client.lean",
        "    discard <| spec.cancel.sleepUntil endsAt\n",
        "    pure ()\n")],
    # A retry is made whatever is left of the deadline, and waited for up to the deadline.
    "notime-ignored": [("LeanHttp/Call.lean",
        "  else if st.backoff < st.remaining clock then .ok st.backoff\n  else .error .noTime\n",
        "  else .ok st.backoff\n")],
    # One connection fewer at once than allowed: four with no limit, one with a limit of two.
    "cap-one-less": [("LeanHttp/Client.lean",
        "    maxActive := config.maxActivePerOrigin }\n",
        "    maxActive := some ((config.maxActivePerOrigin.getD 5) - 1) }\n")],
    # The drain limit is 10 s longer than configured: a body left early waits for its rest.
    "drain-longer": [("LeanHttp/Client.lean",
        "drainBytes := config.drainBytes, drainMs := config.drainMs }",
        "drainBytes := config.drainBytes, drainMs := config.drainMs + 10000 }")],
    # Nothing is drained: every body left early costs its connection.
    "drain-zero": [("LeanHttp/Client.lean",
        "drainBytes := config.drainBytes, drainMs := config.drainMs }",
        "drainBytes := config.drainBytes, drainMs := 0 }")],
    # The end of the callback waits for a read in progress in another task instead of cancelling it.
    "race-waits-read": [("LeanHttp/Body.lean",
        "      if let some transport := transport then\n        transport.cancelRecv true\n      discard <| await done.result?\n      settle false\n",
        "      discard <| await done.result?\n      settle false\n")],
    # The suite calls a helper that does not exist (as it once called `since` before defining it).
    "helper-missing": [("tests/net/run.sh",
        "  since stream-race '^callback entered at '",
        "  sincex stream-race '^callback entered at '")],
}

name = sys.argv[1]
for path, old, new in MUTATIONS[name]:
    p = Path(path)
    s = p.read_text()
    if s.count(old) != 1:
        sys.exit(f"{name}: the text to change occurs {s.count(old)} times in {path}")
    p.write_text(s.replace(old, new))
    print(f"planted {name} in {path}")
