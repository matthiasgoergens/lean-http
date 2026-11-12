The second run of PLAN.txt, on cc23d5c against main 27a0d86, with three variants (main, cancel
without a token, token: a token never cancelled).  Without a token the branch was still slower
(median ratio 1.087), with a token much slower (1.350): result.txt.  That led to 0b65867, which
drops the continuations chained on each call's signal.
