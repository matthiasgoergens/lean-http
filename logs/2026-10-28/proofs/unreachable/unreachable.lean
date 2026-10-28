import Tests.Support.Gen

/-!
The single-step property "no head before the request head is written" needs the invariant `Inv`
(past the sending phase, the request head has been written): from a state that breaks it, which no
run reaches, a step delivers a head with none of the request written.  This builds such a state by
hand and steps it once.
-/

open Std.Http LeanHttp

def main : IO Unit := do
  let c : Case := { script := 0, method := .get, bodySize := 0,
                    config := { keepAlive := true }, deadline := 2000 }
  let .ok prepared := c.prepare | IO.println "refused"
  let (ex, _) := Exchange.begin prepared 0 c.deadline
  -- Unreachable: awaiting the response head with no request byte written.
  let bad := { ex with phase := .awaitingHead, writeInFlight := none, writeBy := none }
  let response := "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n".toUTF8
  let (ex', actions) := bad.step 1 (.received response)
  IO.println s!"headBytes={bad.headBytes} written={bad.written}"
  IO.println s!"actions: {actions.toList.map renderAction}"
  IO.println s!"after: written={ex'.written} terminal={ex'.terminal}"
