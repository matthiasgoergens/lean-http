module

import all LeanHttp.Pool.Proofs

/-!
Prints the axioms of the main theorems about the pool core.  Each must depend on no more than
`propext`, `Classical.choice` and `Quot.sound`, and never on `sorryAx`.

    lake build && lake env lean scripts/pool-axioms.lean
-/

open LeanHttp.Pool

#print axioms wf_empty
#print axioms wf_run
#print axioms WF.not_out_of_idle
#print axioms WF.state_out
#print axioms state_idle
#print axioms state_gone
#print axioms idleCount_run
#print axioms activeCount_run
#print axioms take_reuse
#print axioms take_fresh
#print axioms giveBack_notOut
#print axioms giveBack_out
#print axioms drop_notOut
#print axioms giveBack_not_out
#print axioms giveBack_dropped_gone
#print axioms giveBack_unreusable_gone
#print axioms drop_gone
#print axioms out_step
#print axioms trace_alternates
#print axioms state_gone_apply
#print axioms state_gone_run
#print axioms trace_gone
#print axioms giveBack_unreusable_never_again
#print axioms drop_never_again
#print axioms take_fresh_unused
#print axioms take_closed
#print axioms drop_not_out
#print axioms sweep_letGo
#print axioms letGo_gone
#print axioms apply_closed
#print axioms run_closed
