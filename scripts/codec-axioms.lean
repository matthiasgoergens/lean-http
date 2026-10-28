module

import LeanHttp.Codec.Proofs

/-!
Prints the axioms of the main theorems about the response codec.  Each must depend on no more than
`propext`, `Classical.choice` and `Quot.sound`, and never on `sorryAx`.

    lake build && lake env lean scripts/codec-axioms.lean
-/

open LeanHttp.Codec LeanHttp.Codec.Parser

#print axioms feed_eq_run
#print axioms feed_append
#print axioms feedAll_eq
#print axioms feedSteps_le
#print axioms Parser.stepByte_good
#print axioms Reach.good
#print axioms reach_length_le
#print axioms reach_length_done
#print axioms reach_length_declared
#print axioms reach_head_request
#print axioms reach_noBody_status
#print axioms reach_body_le_max
#print axioms reach_body_after_head
#print axioms Parser.feed_encodeChunked
#print axioms roundtrip_chunked
#print axioms Parser.feed_done
#print axioms Parser.finish_completeCertain
#print axioms Parser.finish_certain_incomplete
#print axioms Parser.reusable_feed
#print axioms Parser.completeCertain_body
#print axioms completeCertain_prefix
#print axioms reach_finish_completeCertain
#print axioms reach_final_head
#print axioms keepAliveOf_close
#print axioms keepAliveOf_malformed
#print axioms keepAliveOf_http10
#print axioms reach_keepAlive
#print axioms Reach.shape
#print axioms reach_shape
#print axioms roundtrip_length
#print axioms roundtrip_untilClose
#print axioms head_sound
#print axioms received_length_declared
#print axioms response_sound
#print axioms feed_respSound
#print axioms chunkedBody_payload_unique
#print axioms headBytes_unique
#print axioms head_sound_unique
#print axioms Parser.feed_noEmptyBody
#print axioms Parser.finish_noEmptyBody
#print axioms reach_response
