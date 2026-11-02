Profiles of net-client making 60000 reused GETs to evil.py's /ok (client on CPU 101, server on CPU
100, no token, trace=0), main 27a0d86 (main.txt) against 99e7983 (cancel.txt): perf record -F 4000
for 8 s on the client process, perf report --sort dso,symbol, the first 80 lines; dso.txt the split
between the kernel and the binary.  About 70% of the samples are in the kernel (scheduling and
context switches between the client's threads); in user space no symbol stands out, the difference
is spread over closure calls (lean_apply_*), objects marked as shared between threads
(lean_mark_mt), allocation and reference counting.
