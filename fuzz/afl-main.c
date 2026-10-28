/*
 * AFL++ entry point for the lean-http fuzzing harness (Fuzz/Harness.lean).
 *
 * Initialises the Lean runtime and the harness module once, then, in AFL++'s persistent mode,
 * hands each input to the exported Lean function `lean_http_fuzz_one`.  An invariant that fails
 * panics in Lean; run with LEAN_ABORT_ON_PANIC=1 so that the panic aborts and AFL++ records a
 * crash (if the panic returns instead, this file aborts).
 *
 * Run by hand with a file argument, the binary checks that one file and exits, which is how
 * crashes are reproduced with the instrumented build.  Must be compiled by an AFL++ compiler.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

lean_object *initialize_lean_x2dhttp_Fuzz_Harness(uint8_t builtin);
uint32_t lean_http_fuzz_one(lean_object *data);

__AFL_FUZZ_INIT();

static void check(const unsigned char *buf, size_t len) {
    lean_object *arr = lean_alloc_sarray(1, len, len);
    memcpy(lean_sarray_cptr(arr), buf, len);
    if (lean_http_fuzz_one(arr) != 0) abort();
}

int main(int argc, char **argv) {
    lean_object *res = initialize_lean_x2dhttp_Fuzz_Harness(1 /* builtin */);
    lean_io_mark_end_initialization();
    if (!lean_io_result_is_ok(res)) {
        lean_io_result_show_error(res);
        lean_dec_ref(res);
        return 1;
    }
    lean_dec_ref(res);
    lean_init_task_manager();

    if (argc > 1 && !getenv("__AFL_SHM_ID")) {
        static unsigned char file_buf[1 << 20];
        FILE *f = fopen(argv[1], "rb");
        if (!f) {
            perror(argv[1]);
            return 1;
        }
        size_t n = fread(file_buf, 1, sizeof file_buf, f);
        fclose(f);
        check(file_buf, n);
        return 0;
    }

    __AFL_INIT();
    unsigned char *buf = __AFL_FUZZ_TESTCASE_BUF;
    while (__AFL_LOOP(100000)) check(buf, (size_t)__AFL_FUZZ_TESTCASE_LEN);
    return 0;
}
