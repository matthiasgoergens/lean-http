The first run of PLAN.txt, on 5612056 (net-client-cancel) against main 27a0d86, with the version
of blocks.sh then: two variants per block (main, cancel without a token), random order.  It found
the branch slower by a median ratio of 1.267 (result.txt), which led to cc23d5c: the client keeps
its calls in a table instead of watching its own token per call.  build.txt is build.sh's output.
