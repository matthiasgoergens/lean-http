Ablations on 3dfd87d, to find what still costs a call without a token, made with the build.sh,
mutate.py and blocks.sh here (blocks.sh takes the variants to run):
- out.txt (25 blocks): main; the branch (cancel); the branch without the table of calls (notrack),
  without asking the tokens in reason? (nocheck), without Live.next's check after its wait
  (nonext), without the mailbox's hook (nohook).  Each removes at most a point or two of the
  slowdown (1.084; 1.059 to 1.074).
- out2.txt (25 blocks): main, main with an unused function added before the client's code
  (mainpert, build-main-pert.sh: the same program with its code placed differently), the branch,
  and the branch with all four removed (all).  mainpert 0.986 (interval 0.967 to 1.034), all 1.052,
  the branch 1.086.
- out3.txt (25 blocks): the branch with the end of the call run in the ending task (sync, an
  EAsync.tryFinally' with sync := true in place of finally): 1.066 against the branch's 1.058, so
  no change, and the change was not kept.
