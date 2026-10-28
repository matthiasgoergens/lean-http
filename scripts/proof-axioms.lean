module

import all LeanHttp.Exchange.Proofs

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
