/*
 * TLS for lean-http: OpenSSL driven over memory BIOs (DESIGN.md, "TLS").
 *
 * OpenSSL never touches a socket here.  The Lean side feeds the session the ciphertext its TCP
 * socket received (lean_http_tls_feed, lean_http_tls_feed_eof), takes the ciphertext the session
 * produced (lean_http_tls_take_output) and sends it with the socket's own asynchronous operations.
 * Every function returns at once: OpenSSL either has the bytes it needs or says it wants more.
 *
 * One task drives a session at a time (LeanHttp.Transport).  Another task may mark it failed while
 * it is driven (lean_http_tls_poison, when a body stream ends during a read), and the lock of each
 * session makes that safe; it is held within one call, which never calls back into Lean or the
 * event loop.  Every OpenSSL operation starts with the thread's error queue cleared and leaves it
 * empty, since tasks move between threads and SSL_get_error reads that queue.
 *
 * The toolchain's C compiler has only the freestanding headers, no libc ones: the lock is a spin
 * lock on a C11 atomic flag (held only for the length of one call), messages are put together by the
 * helpers below, and the two libc functions used are declared here with their standard prototypes.
 */
#include <lean/lean.h>
#include <limits.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>

#include "openssl-min.h"

void *calloc(size_t nmemb, size_t size);
void free(void *ptr);

/* A bounded string, always NUL-terminated. */
typedef struct {
    char *p;
    size_t cap;
    size_t len;
} lh_buf;

static lh_buf lh_buf_of(char *p, size_t cap) {
    lh_buf b = {p, cap, 0};
    p[0] = '\0';
    return b;
}

static void lh_put_n(lh_buf *b, const char *s, size_t n) {
    for (size_t i = 0; i < n && s[i] != '\0' && b->len + 1 < b->cap; i++) b->p[b->len++] = s[i];
    b->p[b->len] = '\0';
}

static void lh_put(lh_buf *b, const char *s) { lh_put_n(b, s, (size_t)-1); }

static void lh_put_hex(lh_buf *b, unsigned long v) {
    char digits[2 * sizeof v + 1];
    int n = 0;
    do {
        digits[n++] = "0123456789abcdef"[v & 0xf];
        v >>= 4;
    } while (v != 0);
    lh_put(b, "0x");
    while (n > 0) {
        char c[2] = {digits[--n], '\0'};
        lh_put(b, c);
    }
}

static void lh_lock(atomic_flag *f) {
    while (atomic_flag_test_and_set_explicit(f, memory_order_acquire)) {
    }
}

static void lh_unlock(atomic_flag *f) { atomic_flag_clear_explicit(f, memory_order_release); }

/* Results of lean_http_tls_handshake; LeanHttp.Tls.HandshakeStep decodes them. */
enum { HS_DONE = 0, HS_WANT_READ = 1, HS_VERIFY = 2, HS_FAILED = 3, HS_CLOSED = 4 };

/* Results of lean_http_tls_read; LeanHttp.Tls.ReadStep decodes them. */
enum { RD_DATA = 0, RD_WANT_READ = 1, RD_CLOSED = 2, RD_TRUNCATED = 3, RD_FAILED = 4 };

typedef struct {
    atomic_flag mu;
    SSL *ssl;
    int eof_fed;    /* the end of TCP input was passed to the session */
    int latched;    /* a read status met after plaintext, returned by the next read; 0 if none */
    int failed;     /* a write or read failed: the session is not used again */
    char err[320];  /* the message of the last failure */
} lh_session;

static lean_external_class *g_ctx_class = NULL;
static lean_external_class *g_session_class = NULL;
static atomic_int g_init_state = 0; /* 0: not started, 1: running, 2: done */
static int g_init_ok = 0;

static void lh_ctx_finalize(void *p) { SSL_CTX_free((SSL_CTX *)p); }

static void lh_session_finalize(void *p) {
    lh_session *s = (lh_session *)p;
    SSL_free(s->ssl); /* frees both BIOs */
    free(s);
}

static void lh_foreach(void *p, b_lean_obj_arg f) {
    (void)p;
    (void)f;
}

/*
 * Initialises OpenSSL before any other call: without its exit handler, so that no clean-up at
 * exit races a finaliser, and without reading openssl.cnf, whose compiled-in path is the
 * toolchain build's Nix store.
 */
static void lh_init_once(void) {
    g_init_ok = OPENSSL_init_ssl(LH_OPENSSL_INIT_NO_ATEXIT | LH_OPENSSL_INIT_NO_LOAD_CONFIG, NULL) == 1;
    ERR_clear_error();
    g_ctx_class = lean_register_external_class(lh_ctx_finalize, lh_foreach);
    g_session_class = lean_register_external_class(lh_session_finalize, lh_foreach);
}

static int lh_init(void) {
    int expected = 0;
    if (atomic_compare_exchange_strong(&g_init_state, &expected, 1)) {
        lh_init_once();
        atomic_store(&g_init_state, 2);
    } else {
        while (atomic_load(&g_init_state) != 2) {
        }
    }
    return g_init_ok;
}

static lean_obj_res lh_error(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

/*
 * Writes the first error of the thread's queue into buf (the reason, without OpenSSL's code and
 * library prefix), or fallback if the queue is empty, and empties the queue.
 */
static void lh_collect(char *buf, size_t len, const char *fallback) {
    unsigned long e, first = 0;
    while ((e = ERR_get_error()) != 0) {
        if (first == 0) first = e;
    }
    lh_buf b = lh_buf_of(buf, len);
    if (first == 0) {
        lh_put(&b, fallback);
        return;
    }
    char tmp[256];
    ERR_error_string_n(first, tmp, sizeof tmp);
    /* "error:0A000086:SSL routines::certificate verify failed": the reason follows the fourth ':'. */
    const char *reason = tmp;
    int colons = 0;
    for (const char *c = tmp; *c != '\0'; c++) {
        if (*c == ':' && ++colons == 4) {
            reason = c + 1;
            break;
        }
    }
    lh_put(&b, *reason != '\0' ? reason : tmp);
}

/* A Lean string as a C string, or NULL if it holds a NUL byte (which C would cut it at). */
static const char *lh_cstr(b_lean_obj_arg s) {
    const char *c = lean_string_cstr(s);
    if (__builtin_strlen(c) != lean_string_size(s) - 1) return NULL;
    return c;
}

static lh_session *lh_sess(b_lean_obj_arg o) { return (lh_session *)lean_get_external_data(o); }

/*
 * LeanHttp.Tls.Context.create (caFile : @& String) (caDirs : @& Array String) : IO Context
 *
 * A client context: TLS 1.2 at least, no renegotiation, no compression, no session tickets, peer
 * verification on with partial wildcards refused and no fallback to the subject's common name,
 * ALPN offering http/1.1 only, and the trust anchors of caFile (if not empty) and of each
 * directory in caDirs (OpenSSL's hashed names).  Fails if OpenSSL is not 3.x or nothing loads.
 */
LEAN_EXPORT lean_obj_res lean_http_tls_ctx_new(b_lean_obj_arg ca_file, b_lean_obj_arg ca_dirs) {
    char buf[512];
    if (!lh_init()) return lh_error("OpenSSL could not be initialised");
    unsigned long v = OpenSSL_version_num();
    if ((v >> 28) != 3) {
        lh_buf b = lh_buf_of(buf, sizeof buf);
        lh_put(&b, "the OpenSSL linked in has version number ");
        lh_put_hex(&b, v);
        lh_put(&b, "; lean-http needs 3.x");
        return lh_error(buf);
    }
    const char *file = lh_cstr(ca_file);
    if (file == NULL) return lh_error("the CA file name contains a NUL byte");
    size_t ndirs = lean_array_size(ca_dirs);
    if (*file == '\0' && ndirs == 0) return lh_error("no CA file or directory was given");
    ERR_clear_error();
    SSL_CTX *ctx = SSL_CTX_new(TLS_client_method());
    if (ctx == NULL) {
        lh_collect(buf, sizeof buf, "SSL_CTX_new failed");
        return lh_error(buf);
    }
    SSL_CTX_set_options(ctx, LH_SSL_OP_NO_RENEGOTIATION | LH_SSL_OP_NO_COMPRESSION | LH_SSL_OP_NO_TICKET);
    if (SSL_CTX_ctrl(ctx, LH_SSL_CTRL_SET_MIN_PROTO_VERSION, LH_TLS1_2_VERSION, NULL) != 1) {
        lh_collect(buf, sizeof buf, "cannot set TLS 1.2 as the minimum version");
        SSL_CTX_free(ctx);
        return lh_error(buf);
    }
    SSL_CTX_ctrl(ctx, LH_SSL_CTRL_MODE, LH_SSL_MODE_RELEASE_BUFFERS, NULL);
    SSL_CTX_set_verify(ctx, LH_SSL_VERIFY_PEER, NULL);
    X509_VERIFY_PARAM *param = SSL_CTX_get0_param(ctx);
    X509_VERIFY_PARAM_set_hostflags(param,
        LH_X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS | LH_X509_CHECK_FLAG_NEVER_CHECK_SUBJECT);
    if (X509_VERIFY_PARAM_set_flags(param, LH_X509_V_FLAG_PARTIAL_CHAIN) != 1) {
        lh_collect(buf, sizeof buf, "cannot set the verification flags");
        SSL_CTX_free(ctx);
        return lh_error(buf);
    }
    static const unsigned char alpn[] = {8, 'h', 't', 't', 'p', '/', '1', '.', '1'};
    /* SSL_CTX_set_alpn_protos returns 0 on success. */
    if (SSL_CTX_set_alpn_protos(ctx, alpn, sizeof alpn) != 0) {
        lh_collect(buf, sizeof buf, "cannot set ALPN");
        SSL_CTX_free(ctx);
        return lh_error(buf);
    }
    if (*file != '\0' && SSL_CTX_load_verify_file(ctx, file) != 1) {
        char reason[256];
        lh_collect(reason, sizeof reason, "no certificate in it");
        lh_buf b = lh_buf_of(buf, sizeof buf);
        lh_put(&b, "cannot load the CA file ");
        lh_put(&b, file);
        lh_put(&b, ": ");
        lh_put(&b, reason);
        SSL_CTX_free(ctx);
        return lh_error(buf);
    }
    for (size_t i = 0; i < ndirs; i++) {
        const char *dir = lh_cstr(lean_array_get_core(ca_dirs, i));
        if (dir == NULL || SSL_CTX_load_verify_dir(ctx, dir) != 1) {
            char reason[256];
            lh_collect(reason, sizeof reason, dir == NULL ? "its name contains a NUL byte" : "it cannot be used");
            lh_buf b = lh_buf_of(buf, sizeof buf);
            lh_put(&b, "cannot use the CA directory ");
            lh_put(&b, dir == NULL ? "?" : dir);
            lh_put(&b, ": ");
            lh_put(&b, reason);
            SSL_CTX_free(ctx);
            return lh_error(buf);
        }
    }
    ERR_clear_error();
    return lean_io_result_mk_ok(lean_alloc_external(g_ctx_class, ctx));
}

/*
 * LeanHttp.Tls.Session.create (ctx : @& Context) (host : @& String) (isIp : UInt8) : IO Session
 *
 * A client session over two memory BIOs.  For a host name: SNI carries it and the certificate's
 * DNS names must match it.  For an IP literal (without brackets): no SNI, and the certificate must
 * carry the address.  The Lean side has already refused names that cannot be checked; this only
 * refuses what OpenSSL refuses, and an empty name, which would turn the name check off.
 */
LEAN_EXPORT lean_obj_res lean_http_tls_session_new(b_lean_obj_arg ctx_obj, b_lean_obj_arg host_obj, uint8_t is_ip) {
    char buf[512];
    const char *host = lh_cstr(host_obj);
    if (host == NULL || *host == '\0') return lh_error("the server name is empty or contains a NUL byte");
    SSL_CTX *ctx = (SSL_CTX *)lean_get_external_data(ctx_obj);
    ERR_clear_error();
    SSL *ssl = SSL_new(ctx);
    if (ssl == NULL) {
        lh_collect(buf, sizeof buf, "SSL_new failed");
        return lh_error(buf);
    }
    BIO *rbio = BIO_new(BIO_s_mem());
    BIO *wbio = BIO_new(BIO_s_mem());
    if (rbio == NULL || wbio == NULL) {
        /* BIO_free is not declared; SSL_set_bio hands the BIOs to the session, which frees them. */
        SSL_set_bio(ssl, rbio, wbio);
        SSL_free(ssl);
        ERR_clear_error();
        return lh_error("cannot allocate memory BIOs");
    }
    SSL_set_bio(ssl, rbio, wbio);
    SSL_set_connect_state(ssl);
    int ok;
    if (is_ip) {
        ok = X509_VERIFY_PARAM_set1_ip_asc(SSL_get0_param(ssl), host) == 1;
    } else {
        ok = SSL_ctrl(ssl, LH_SSL_CTRL_SET_TLSEXT_HOSTNAME, LH_TLSEXT_NAMETYPE_host_name, (void *)host) == 1
            && SSL_set1_host(ssl, host) == 1;
    }
    if (!ok) {
        char reason[256];
        lh_collect(reason, sizeof reason, "refused");
        lh_buf b = lh_buf_of(buf, sizeof buf);
        lh_put(&b, "cannot set the server name ");
        lh_put(&b, host);
        lh_put(&b, ": ");
        lh_put(&b, reason);
        SSL_free(ssl);
        return lh_error(buf);
    }
    lh_session *s = (lh_session *)calloc(1, sizeof *s);
    if (s == NULL) {
        SSL_free(ssl);
        return lh_error("out of memory");
    }
    atomic_flag_clear(&s->mu);
    s->ssl = ssl;
    ERR_clear_error();
    return lean_io_result_mk_ok(lean_alloc_external(g_session_class, s));
}

/*
 * LeanHttp.Tls.Session.handshakeStep (s : @& Session) : IO UInt32
 *
 * Advances the handshake with the input fed so far.  HS_DONE once it is complete (and ALPN, if the
 * server chose a protocol, chose http/1.1); HS_WANT_READ when it needs more input; otherwise why it
 * failed: HS_VERIFY (the certificate or the name), HS_CLOSED (the connection ended during it),
 * HS_FAILED (an alert or a protocol failure), with the message in lean_http_tls_last_error.  The
 * output it produced is taken with lean_http_tls_take_output.
 */
LEAN_EXPORT lean_obj_res lean_http_tls_handshake(b_lean_obj_arg o) {
    lh_session *s = lh_sess(o);
    lh_lock(&s->mu);
    ERR_clear_error();
    uint32_t code;
    int rc = SSL_do_handshake(s->ssl);
    if (rc == 1) {
        const unsigned char *proto = NULL;
        unsigned int len = 0;
        SSL_get0_alpn_selected(s->ssl, &proto, &len);
        if (len > 0 && !(len == 8 && __builtin_memcmp(proto, "http/1.1", 8) == 0)) {
            lh_buf b = lh_buf_of(s->err, sizeof s->err);
            lh_put(&b, "the server chose the ALPN protocol ");
            lh_put_n(&b, (const char *)proto, len);
            lh_put(&b, ", not http/1.1");
            s->failed = 1;
            code = HS_FAILED;
        } else {
            code = HS_DONE;
        }
    } else {
        int e = SSL_get_error(s->ssl, rc);
        long verify = SSL_get_verify_result(s->ssl);
        if (e == LH_SSL_ERROR_WANT_READ || e == LH_SSL_ERROR_WANT_WRITE) {
            code = HS_WANT_READ;
        } else if (verify != LH_X509_V_OK) {
            lh_buf b = lh_buf_of(s->err, sizeof s->err);
            lh_put(&b, X509_verify_cert_error_string(verify));
            s->failed = 1;
            code = HS_VERIFY;
        } else if (e == LH_SSL_ERROR_ZERO_RETURN || s->eof_fed) {
            lh_collect(s->err, sizeof s->err, "the server closed the connection");
            s->failed = 1;
            code = HS_CLOSED;
        } else {
            lh_collect(s->err, sizeof s->err, "the handshake failed");
            s->failed = 1;
            code = HS_FAILED;
        }
    }
    ERR_clear_error();
    lh_unlock(&s->mu);
    return lean_io_result_mk_ok(lean_box_uint32(code));
}

/* LeanHttp.Tls.Session.feed (s : @& Session) (bytes : @& ByteArray) : IO Unit */
LEAN_EXPORT lean_obj_res lean_http_tls_feed(b_lean_obj_arg o, b_lean_obj_arg bytes) {
    lh_session *s = lh_sess(o);
    size_t n = lean_sarray_size(bytes);
    if (n == 0) return lean_io_result_mk_ok(lean_box(0));
    if (n > INT_MAX) return lh_error("TLS input too large");
    lh_lock(&s->mu);
    ERR_clear_error();
    int rc = BIO_write(SSL_get_rbio(s->ssl), lean_sarray_cptr(bytes), (int)n);
    if (rc != (int)n && !s->failed) {
        s->failed = 1;
        lh_buf b = lh_buf_of(s->err, sizeof s->err);
        lh_put(&b, "TLS: cannot buffer the input");
    }
    ERR_clear_error();
    lh_unlock(&s->mu);
    if (rc != (int)n) return lh_error("TLS: cannot buffer the input");
    return lean_io_result_mk_ok(lean_box(0));
}

/*
 * LeanHttp.Tls.Session.feedEof (s : @& Session) : IO Unit
 *
 * The end of TCP input: once the read BIO is empty, OpenSSL sees the end of input instead of
 * waiting for more.
 */
LEAN_EXPORT lean_obj_res lean_http_tls_feed_eof(b_lean_obj_arg o) {
    lh_session *s = lh_sess(o);
    lh_lock(&s->mu);
    BIO_ctrl(SSL_get_rbio(s->ssl), LH_BIO_C_SET_BUF_MEM_EOF_RETURN, 0, NULL);
    s->eof_fed = 1;
    ERR_clear_error();
    lh_unlock(&s->mu);
    return lean_io_result_mk_ok(lean_box(0));
}

/* LeanHttp.Tls.Session.takeOutput (s : @& Session) : IO ByteArray: the ciphertext to send, in order. */
LEAN_EXPORT lean_obj_res lean_http_tls_take_output(b_lean_obj_arg o) {
    lh_session *s = lh_sess(o);
    lh_lock(&s->mu);
    BIO *w = SSL_get_wbio(s->ssl);
    size_t n = BIO_ctrl_pending(w);
    if (n > INT_MAX) n = INT_MAX;
    lean_object *out = lean_alloc_sarray(1, 0, n);
    int got = n > 0 ? BIO_read(w, lean_sarray_cptr(out), (int)n) : 0;
    lean_to_sarray(out)->m_size = got > 0 ? (size_t)got : 0;
    ERR_clear_error();
    lh_unlock(&s->mu);
    return lean_io_result_mk_ok(out);
}

/*
 * LeanHttp.Tls.Session.write (s : @& Session) (bytes : @& ByteArray) : IO Unit
 *
 * Encrypts bytes; the ciphertext is taken with lean_http_tls_take_output.  With memory BIOs a
 * write after the handshake completes in full or fails.
 */
LEAN_EXPORT lean_obj_res lean_http_tls_write(b_lean_obj_arg o, b_lean_obj_arg bytes) {
    lh_session *s = lh_sess(o);
    size_t n = lean_sarray_size(bytes);
    if (n == 0) return lean_io_result_mk_ok(lean_box(0));
    if (n > INT_MAX) return lh_error("TLS write too large");
    char buf[sizeof s->err];
    lh_lock(&s->mu);
    int ok = 0;
    if (s->failed) {
        lh_buf b = lh_buf_of(buf, sizeof buf);
        lh_put(&b, "TLS: the connection already failed (");
        lh_put(&b, s->err);
        lh_put(&b, ")");
    } else {
        ERR_clear_error();
        int rc = SSL_write(s->ssl, lean_sarray_cptr(bytes), (int)n);
        if (rc == (int)n) {
            ok = 1;
        } else {
            char reason[256];
            lh_collect(reason, sizeof reason, "the write failed");
            lh_buf e = lh_buf_of(s->err, sizeof s->err);
            lh_put(&e, "TLS write failed: ");
            lh_put(&e, reason);
            s->failed = 1;
            lh_buf b = lh_buf_of(buf, sizeof buf);
            lh_put(&b, s->err);
        }
        ERR_clear_error();
    }
    lh_unlock(&s->mu);
    if (!ok) return lh_error(buf);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Records why a read ended without data, and returns its status. */
static uint32_t lh_read_end(lh_session *s, int e) {
    if (e == LH_SSL_ERROR_ZERO_RETURN) {
        ERR_clear_error();
        return RD_CLOSED;
    }
    s->failed = 1;
    if (s->eof_fed && !(SSL_get_shutdown(s->ssl) & LH_SSL_RECEIVED_SHUTDOWN)) {
        char reason[256];
        lh_collect(reason, sizeof reason, "unexpected end of input");
        lh_buf b = lh_buf_of(s->err, sizeof s->err);
        lh_put(&b, "TLS: the server ended the connection without close_notify, so the response may be truncated (");
        lh_put(&b, reason);
        lh_put(&b, ")");
        return RD_TRUNCATED;
    }
    char reason[256];
    lh_collect(reason, sizeof reason, "the read failed");
    lh_buf b = lh_buf_of(s->err, sizeof s->err);
    lh_put(&b, "TLS: ");
    lh_put(&b, reason);
    return RD_FAILED;
}

/*
 * LeanHttp.Tls.Session.read (s : @& Session) (max : USize) : IO (UInt32 × ByteArray)
 *
 * Decrypts up to max bytes from every record the input fed so far holds: SSL_read returns at most
 * one record, so it is called until max bytes are read or the session wants more input.  Returns
 * RD_DATA with the bytes; or, with none, RD_WANT_READ, RD_CLOSED (the server's close_notify),
 * RD_TRUNCATED (the end of input without close_notify) or RD_FAILED (an alert or a protocol
 * failure), the message in lean_http_tls_last_error.  An end met after some bytes is kept and
 * returned by the next read.  Output the reading produced (a key update's reply) is taken with
 * lean_http_tls_take_output.
 */
LEAN_EXPORT lean_obj_res lean_http_tls_read(b_lean_obj_arg o, size_t max) {
    lh_session *s = lh_sess(o);
    if (max == 0) max = 1;
    if (max > INT_MAX) max = INT_MAX;
    size_t total = 0;
    uint32_t status = RD_WANT_READ;
    lh_lock(&s->mu);
    /* Nothing buffered and the input not ended: no buffer is allocated for a read that would wait. */
    int idle = s->latched == 0 && !s->failed && !s->eof_fed && !SSL_has_pending(s->ssl)
        && BIO_ctrl_pending(SSL_get_rbio(s->ssl)) == 0;
    lean_object *out = lean_alloc_sarray(1, 0, idle || s->latched != 0 || s->failed ? 0 : max);
    uint8_t *buf = lean_sarray_cptr(out);
    if (idle) {
        /* status stays RD_WANT_READ */
    } else if (s->latched != 0) {
        status = (uint32_t)s->latched;
        s->latched = 0;
    } else if (s->failed) {
        status = RD_FAILED;
    } else {
        while (total < max) {
            ERR_clear_error();
            int n = SSL_read(s->ssl, buf + total, (int)(max - total));
            if (n > 0) {
                total += (size_t)n;
                continue;
            }
            int e = SSL_get_error(s->ssl, n);
            if (e == LH_SSL_ERROR_WANT_READ || e == LH_SSL_ERROR_WANT_WRITE) break;
            uint32_t end = lh_read_end(s, e);
            if (total > 0) s->latched = (int)end;
            else status = end;
            break;
        }
        if (total > 0) status = RD_DATA;
    }
    ERR_clear_error();
    lh_unlock(&s->mu);
    lean_to_sarray(out)->m_size = total;
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_box_uint32(status));
    lean_ctor_set(pair, 1, out);
    return lean_io_result_mk_ok(pair);
}

/*
 * LeanHttp.Tls.Session.clean (s : @& Session) : IO Bool
 *
 * Whether the session holds nothing: no plaintext or ciphertext buffered (SSL_has_pending, the
 * read BIO empty), no close_notify received, no end of input fed, no end kept for the next read,
 * and no failure.  Only such a connection may go back to the pool.
 */
LEAN_EXPORT lean_obj_res lean_http_tls_clean(b_lean_obj_arg o) {
    lh_session *s = lh_sess(o);
    lh_lock(&s->mu);
    int clean = !s->failed && !s->eof_fed && s->latched == 0
        && SSL_is_init_finished(s->ssl)
        && !SSL_has_pending(s->ssl)
        && BIO_ctrl_pending(SSL_get_rbio(s->ssl)) == 0
        && !(SSL_get_shutdown(s->ssl) & LH_SSL_RECEIVED_SHUTDOWN);
    ERR_clear_error();
    lh_unlock(&s->mu);
    return lean_io_result_mk_ok(lean_box(clean ? 1 : 0));
}

/*
 * LeanHttp.Tls.Session.poison (s : @& Session) : IO Unit
 *
 * Marks the session failed: a read was given up while ciphertext may have been taken from the
 * socket and not fed, so the session no longer matches the stream and must not be reused.
 */
LEAN_EXPORT lean_obj_res lean_http_tls_poison(b_lean_obj_arg o) {
    lh_session *s = lh_sess(o);
    lh_lock(&s->mu);
    if (!s->failed) {
        s->failed = 1;
        lh_buf b = lh_buf_of(s->err, sizeof s->err);
        lh_put(&b, "TLS: a read was given up, so the connection is not reused");
    }
    lh_unlock(&s->mu);
    return lean_io_result_mk_ok(lean_box(0));
}

/*
 * LeanHttp.Tls.Session.closeNotify (s : @& Session) : IO Unit
 *
 * Queues close_notify, once, on a session whose handshake completed and that has not failed; the
 * alert is taken with lean_http_tls_take_output.
 */
LEAN_EXPORT lean_obj_res lean_http_tls_close_notify(b_lean_obj_arg o) {
    lh_session *s = lh_sess(o);
    lh_lock(&s->mu);
    if (!s->failed && SSL_is_init_finished(s->ssl) && !(SSL_get_shutdown(s->ssl) & LH_SSL_SENT_SHUTDOWN)) {
        ERR_clear_error();
        (void)SSL_shutdown(s->ssl);
    }
    ERR_clear_error();
    lh_unlock(&s->mu);
    return lean_io_result_mk_ok(lean_box(0));
}

/* LeanHttp.Tls.Session.lastError (s : @& Session) : IO String */
LEAN_EXPORT lean_obj_res lean_http_tls_last_error(b_lean_obj_arg o) {
    lh_session *s = lh_sess(o);
    lh_lock(&s->mu);
    lean_object *r = lean_mk_string(s->err);
    lh_unlock(&s->mu);
    return lean_io_result_mk_ok(r);
}

/* LeanHttp.Tls.Session.version (s : @& Session) : IO String: "TLSv1.3", for instance. */
LEAN_EXPORT lean_obj_res lean_http_tls_version(b_lean_obj_arg o) {
    lh_session *s = lh_sess(o);
    lh_lock(&s->mu);
    const char *v = SSL_get_version(s->ssl);
    lean_object *r = lean_mk_string(v != NULL ? v : "");
    lh_unlock(&s->mu);
    return lean_io_result_mk_ok(r);
}

/* LeanHttp.Tls.opensslVersionNumber : IO UInt64: OPENSSL_VERSION_NUMBER of the OpenSSL linked in. */
LEAN_EXPORT lean_obj_res lean_http_tls_openssl_version(lean_obj_arg unit) {
    (void)unit;
    lh_init();
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)OpenSSL_version_num()));
}
