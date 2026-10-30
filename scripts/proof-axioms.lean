module

import all LeanHttp.Exchange.Proofs
import all LeanHttp.Exchange.Liveness
import all LeanHttp.Exchange.Response

/-!
Prints the axioms of the main theorems about the exchange core.  Each must depend on no more than
`propext`, `Classical.choice` and `Quot.sound`, and never on `sorryAx`.

    lake build && lake env lean scripts/proof-axioms.lean
-/

open LeanHttp.Exchange

#print axioms step_of_terminal
#print axioms step_stale_tick
#print axioms step_deliverHead
#print axioms step_finish_reusable
#print axioms step_fail
#print axioms delivery_iff
#print axioms step_ends
#print axioms step_writes
#print axioms step_reads
#print axioms step_chunk_after_head
#print axioms step_unsolicited
#print axioms Reachable.inv
#print axioms Run.inFlight
#print axioms Reachable.beforeDeadline
#print axioms step_deadline
#print axioms Observed.agrees
#print axioms observed_fail
#print axioms observed_write
#print axioms Observed.clock
#print axioms observed_finish_reusable
#print axioms observed_deadline
#print axioms begin_ends
#print axioms begin_write
#print axioms begin_fail
#print axioms Reachable.timers
#print axioms Reachable.ahead
#print axioms Reachable.deadlineAhead
#print axioms ObservedMono.deadlineAhead
#print axioms Reachable.tick_due
#print axioms Reachable.due_advances
#print axioms Reachable.dueCount_le
#print axioms Reachable.dueCount_bound
#print axioms Reachable.ended_after_waits
#print axioms Reachable.ended_at_deadline
#print axioms Reachable.ends_of_fair
#print axioms Reachable.ends_of_allDue
#print axioms step_empty_received
#print axioms Observed.cinv
#print axioms observed_finish_codec
#print axioms observed_finish_complete
#print axioms observed_body_prefix
#print axioms step_pulls
#print axioms PullRun.inFlight
#print axioms observed_pull
#print axioms observed_notSent_unpulled
#print axioms Observed.framed
#print axioms observed_length_written
#print axioms observed_finish_body
#print axioms accept_length
#print axioms step_broken
