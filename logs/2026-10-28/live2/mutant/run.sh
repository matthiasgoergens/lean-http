#!/usr/bin/env bash
# Inside the container: the checker against a mutant core in which an empty read completes the read
# (the behaviour before this change), to see that the new trace and property catch it.
lake build core-tests 2>&1 | tail -n 1
echo '$ core-tests traces'; .lake/build/bin/core-tests traces | grep -v '^PASS'; echo "exit status $?"
echo '$ core-tests props 20000 1'; .lake/build/bin/core-tests props 20000 1 | head -n 12; echo "exit status $?"
echo '$ core-tests props 20000 1 --skip "one read in flight"'
.lake/build/bin/core-tests props 20000 1 --skip "one read in flight" | head -n 12; echo "exit status $?"
