Runs of 20 blocks, the same three variants: out-nopromise-20.txt on e0be965 (no promise for a call
without a token: 1.025, interval 0.965 to 1.087; with a token 1.213), out-3dfd87d-20.txt on 3dfd87d
(the token's waiter registered directly: 1.105 without a token, 1.140 with one).  A run of 50
blocks on 3dfd87d (1.076, interval 1.023 to 1.120, without a token; 1.140, 1.116 to 1.178, with
one) had its raw output overwritten by mistake and is not kept; the final run (../out.txt) repeats
the measurement on the final commit.
