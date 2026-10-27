set pagination off
set confirm off
set breakpoint pending on
break uv_read_start
commands
silent
printf "== uv_read_start (thread %d)\n", $_thread
bt 5
continue
end
break uv_read_stop
commands
silent
printf "== uv_read_stop (thread %d)\n", $_thread
bt 5
continue
end
break lean_uv_tcp_cancel_recv
commands
silent
printf "== cancelRecv (thread %d)\n", $_thread
continue
end
break lean_uv_tcp_recv
commands
silent
printf "== recv? (thread %d)\n", $_thread
continue
end
break lean_uv_tcp_wait_readable
commands
silent
printf "== waitReadable (thread %d)\n", $_thread
continue
end
break lean_finalize_task_manager
commands
silent
printf "== lean_finalize_task_manager entered (main returned)\n"
continue
end
run
