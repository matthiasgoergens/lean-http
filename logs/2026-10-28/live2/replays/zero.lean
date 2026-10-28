import LeanHttp

/-!
An exchange configuration with a zero gap, written as a literal: `gapMs_pos` cannot be proved, so
this must fail to elaborate.  The one with a gap of 1 ms must elaborate.
-/

open LeanHttp

def oneGap : ExchangeConfig := { gapMs := 1 }

def zeroGap : ExchangeConfig := { gapMs := 0 }
