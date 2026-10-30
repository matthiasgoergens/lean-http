/*
 * Checks native/openssl-min.h against OpenSSL's real headers: compile with
 *
 *   cc -std=c11 -Werror -fsyntax-only -I <OpenSSL include dir> native/openssl-check.c
 *
 * Each prototype of openssl-min.h redeclares one of OpenSSL's, so a prototype that differs is a
 * "conflicting types" error; each typedef must name the same type; and each constant is compared
 * with OpenSSL's.  The macros native/tls.c reaches through *_ctrl functions are checked by their
 * control numbers below; their expansions were read from OpenSSL's headers (bio.h, ssl.h, tls1.h).
 */
#include <openssl/bio.h>
#include <openssl/crypto.h>
#include <openssl/err.h>
#include <openssl/ssl.h>
#include <openssl/tls1.h>
#include <openssl/x509_vfy.h>
#include <openssl/x509v3.h>

#include "openssl-min.h"

#if OPENSSL_VERSION_MAJOR != 3
#error "openssl-min.h declares the OpenSSL 3 ABI"
#endif

#define SAME(ours, theirs) _Static_assert((ours) == (theirs), #ours " differs from OpenSSL's " #theirs)

SAME(LH_OPENSSL_INIT_NO_LOAD_CONFIG, OPENSSL_INIT_NO_LOAD_CONFIG);
SAME(LH_OPENSSL_INIT_NO_ATEXIT, OPENSSL_INIT_NO_ATEXIT);
SAME(LH_SSL_OP_NO_TICKET, SSL_OP_NO_TICKET);
SAME(LH_SSL_OP_NO_COMPRESSION, SSL_OP_NO_COMPRESSION);
SAME(LH_SSL_OP_NO_RENEGOTIATION, SSL_OP_NO_RENEGOTIATION);
SAME(LH_SSL_CTRL_MODE, SSL_CTRL_MODE);
SAME(LH_SSL_CTRL_SET_TLSEXT_HOSTNAME, SSL_CTRL_SET_TLSEXT_HOSTNAME);
SAME(LH_SSL_CTRL_SET_MIN_PROTO_VERSION, SSL_CTRL_SET_MIN_PROTO_VERSION);
SAME(LH_TLSEXT_NAMETYPE_host_name, TLSEXT_NAMETYPE_host_name);
SAME(LH_TLS1_2_VERSION, TLS1_2_VERSION);
SAME(LH_SSL_MODE_RELEASE_BUFFERS, SSL_MODE_RELEASE_BUFFERS);
SAME(LH_SSL_VERIFY_PEER, SSL_VERIFY_PEER);
SAME(LH_X509_V_OK, X509_V_OK);
SAME(LH_X509_V_FLAG_PARTIAL_CHAIN, X509_V_FLAG_PARTIAL_CHAIN);
SAME(LH_X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS, X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS);
SAME(LH_X509_CHECK_FLAG_NEVER_CHECK_SUBJECT, X509_CHECK_FLAG_NEVER_CHECK_SUBJECT);
SAME(LH_SSL_ERROR_NONE, SSL_ERROR_NONE);
SAME(LH_SSL_ERROR_SSL, SSL_ERROR_SSL);
SAME(LH_SSL_ERROR_WANT_READ, SSL_ERROR_WANT_READ);
SAME(LH_SSL_ERROR_WANT_WRITE, SSL_ERROR_WANT_WRITE);
SAME(LH_SSL_ERROR_SYSCALL, SSL_ERROR_SYSCALL);
SAME(LH_SSL_ERROR_ZERO_RETURN, SSL_ERROR_ZERO_RETURN);
SAME(LH_SSL_SENT_SHUTDOWN, SSL_SENT_SHUTDOWN);
SAME(LH_SSL_RECEIVED_SHUTDOWN, SSL_RECEIVED_SHUTDOWN);
SAME(LH_BIO_CTRL_PENDING, BIO_CTRL_PENDING);
SAME(LH_BIO_C_SET_BUF_MEM_EOF_RETURN, BIO_C_SET_BUF_MEM_EOF_RETURN);

/* The macros tls.c replaces, expanded the way tls.c calls them: these must compile to the same calls. */
static void same_expansions(SSL_CTX *ctx, SSL *ssl, BIO *bio) {
    (void)SSL_CTX_set_min_proto_version(ctx, TLS1_2_VERSION);
    (void)SSL_CTX_ctrl(ctx, LH_SSL_CTRL_SET_MIN_PROTO_VERSION, LH_TLS1_2_VERSION, NULL);
    (void)SSL_CTX_set_mode(ctx, SSL_MODE_RELEASE_BUFFERS);
    (void)SSL_CTX_ctrl(ctx, LH_SSL_CTRL_MODE, LH_SSL_MODE_RELEASE_BUFFERS, NULL);
    (void)SSL_set_tlsext_host_name(ssl, "example.com");
    (void)SSL_ctrl(ssl, LH_SSL_CTRL_SET_TLSEXT_HOSTNAME, LH_TLSEXT_NAMETYPE_host_name, (void *)"example.com");
    (void)BIO_set_mem_eof_return(bio, 0);
    (void)BIO_ctrl(bio, LH_BIO_C_SET_BUF_MEM_EOF_RETURN, 0, NULL);
}

int main(void) {
    (void)same_expansions;
    return 0;
}
