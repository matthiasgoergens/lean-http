set pagination off
set confirm off
set breakpoint pending on
break lean_uv_tcp_cancel_recv
commands
silent
printf "== cancelRecv called (promise_read set? see bt)\n"
bt 12
continue
end
break lean_uv_tcp_recv
commands
silent
printf "== recv? called\n"
bt 6
continue
end
break lean_uv_tcp_wait_readable
commands
silent
printf "== waitReadable called\n"
bt 4
continue
end
break lean_finalize_task_manager
commands
silent
printf "== lean_finalize_task_manager entered (main returned)\n"
continue
end
run
