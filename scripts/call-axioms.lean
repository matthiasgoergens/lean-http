module

import all LeanHttp.Call.Proofs

/-!
Prints the axioms of the main theorems about the per-call planner.  Each must depend on no more than
`propext`, `Classical.choice` and `Quot.sound`, and never on `sorryAx`.

    lake build && lake env lean scripts/call-axioms.lean
-/

open LeanHttp.Call

#print axioms LeanHttp.Backoff.delayMs_le_cap
#print axioms toList_ofList
#print axioms plan_follow_credentials
#print axioms Reachable.credentials
#print axioms Reachable.hops_le
#print axioms plan_hop_limit
#print axioms plan_no_resend
#print axioms plan_localClose
#print axioms plan_retry_delay
#print axioms plan_retry_same_hop
#print axioms plan_follow_303
#print axioms plan_follow_method_change
#print axioms plan_follow_host
#print axioms Reachable.retries_le
#print axioms plan_follow_new_hop
#print axioms plan_follow_replayable
#print axioms plan_retry_status
#print axioms plan_no_follow
#print axioms Reachable.target
#print axioms Reachable.emptyBody
#print axioms originKey_ne_of_scheme
#print axioms originKey_ne_of_port
#print axioms plan_follow_keeps_empty
#print axioms plan_refused_delivered
#print axioms plan_off_delivered
#print axioms plan_no_retry
#print axioms plan_follow_cross_origin
#print axioms Reachable.scheme
