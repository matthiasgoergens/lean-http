/*
 * The OpenSSL 3 functions and constants native/tls.c uses, declared by hand.
 *
 * The Lean toolchain links every executable with its own static OpenSSL (lib/libssl.a and
 * lib/libcrypto.a, 3.6.0 in the Linux toolchains from v4.34.1 on) but ships no OpenSSL headers.
 * OpenSSL keeps its ABI stable within a major version, so the declarations below, all of
 * functions present since 3.0, hold for any 3.x.  native/openssl-check.c includes OpenSSL's real
 * headers and this file together, so that a prototype that differs is a compile error, and
 * compares every constant with OpenSSL's; scripts/ci.sh runs it (stage "tls-abi").
 *
 * The struct tags are OpenSSL's own, so that the typedefs coincide with OpenSSL's in the check.
 * Interfaces that OpenSSL defines as macros are reached through the functions they expand to,
 * with the constants named here (LH_ prefix); inline functions of OpenSSL's headers are not used.
 */
#ifndef LEAN_HTTP_OPENSSL_MIN_H
#define LEAN_HTTP_OPENSSL_MIN_H

#include <stddef.h>
#include <stdint.h>

typedef struct ssl_st SSL;
typedef struct ssl_ctx_st SSL_CTX;
typedef struct ssl_method_st SSL_METHOD;
typedef struct bio_st BIO;
typedef struct bio_method_st BIO_METHOD;
typedef struct x509_store_ctx_st X509_STORE_CTX;
typedef struct X509_VERIFY_PARAM_st X509_VERIFY_PARAM;
typedef struct ossl_init_settings_st OPENSSL_INIT_SETTINGS;
typedef int (*SSL_verify_cb)(int preverify_ok, X509_STORE_CTX *x509_ctx);

/* Library */
int OPENSSL_init_ssl(uint64_t opts, const OPENSSL_INIT_SETTINGS *settings);
unsigned long OpenSSL_version_num(void);

/* Contexts */
const SSL_METHOD *TLS_client_method(void);
SSL_CTX *SSL_CTX_new(const SSL_METHOD *meth);
void SSL_CTX_free(SSL_CTX *ctx);
uint64_t SSL_CTX_set_options(SSL_CTX *ctx, uint64_t op);
long SSL_CTX_ctrl(SSL_CTX *ctx, int cmd, long larg, void *parg);
void SSL_CTX_set_verify(SSL_CTX *ctx, int mode, SSL_verify_cb callback);
int SSL_CTX_load_verify_file(SSL_CTX *ctx, const char *CAfile);
int SSL_CTX_load_verify_dir(SSL_CTX *ctx, const char *CApath);
X509_VERIFY_PARAM *SSL_CTX_get0_param(SSL_CTX *ctx);
int SSL_CTX_set_alpn_protos(SSL_CTX *ctx, const unsigned char *protos, unsigned int protos_len);
int X509_VERIFY_PARAM_set_flags(X509_VERIFY_PARAM *param, unsigned long flags);
void X509_VERIFY_PARAM_set_hostflags(X509_VERIFY_PARAM *param, unsigned int flags);

/* Sessions */
SSL *SSL_new(SSL_CTX *ctx);
void SSL_free(SSL *ssl);
void SSL_set_bio(SSL *s, BIO *rbio, BIO *wbio);
void SSL_set_connect_state(SSL *s);
long SSL_ctrl(SSL *ssl, int cmd, long larg, void *parg);
int SSL_set1_host(SSL *s, const char *host);
X509_VERIFY_PARAM *SSL_get0_param(SSL *ssl);
int X509_VERIFY_PARAM_set1_ip_asc(X509_VERIFY_PARAM *param, const char *ipasc);
int SSL_do_handshake(SSL *s);
int SSL_read(SSL *ssl, void *buf, int num);
int SSL_write(SSL *ssl, const void *buf, int num);
int SSL_get_error(const SSL *s, int ret_code);
int SSL_shutdown(SSL *s);
int SSL_get_shutdown(const SSL *ssl);
int SSL_has_pending(const SSL *s);
int SSL_is_init_finished(const SSL *s);
long SSL_get_verify_result(const SSL *ssl);
const char *X509_verify_cert_error_string(long n);
const char *SSL_get_version(const SSL *s);
void SSL_get0_alpn_selected(const SSL *ssl, const unsigned char **data, unsigned int *len);
BIO *SSL_get_rbio(const SSL *s);
BIO *SSL_get_wbio(const SSL *s);

/* Memory BIOs */
const BIO_METHOD *BIO_s_mem(void);
BIO *BIO_new(const BIO_METHOD *type);
int BIO_write(BIO *b, const void *data, int dlen);
int BIO_read(BIO *b, void *data, int dlen);
long BIO_ctrl(BIO *bp, int cmd, long larg, void *parg);
size_t BIO_ctrl_pending(BIO *b);

/* Errors */
unsigned long ERR_get_error(void);
void ERR_clear_error(void);
void ERR_error_string_n(unsigned long e, char *buf, size_t len);

/* Constants, each compared with OpenSSL's own by native/openssl-check.c. */
#define LH_OPENSSL_INIT_NO_LOAD_CONFIG 0x00000080L
#define LH_OPENSSL_INIT_NO_ATEXIT 0x00080000L

#define LH_SSL_OP_NO_TICKET ((uint64_t)1 << 14)
#define LH_SSL_OP_NO_COMPRESSION ((uint64_t)1 << 17)
#define LH_SSL_OP_NO_RENEGOTIATION ((uint64_t)1 << 30)

#define LH_SSL_CTRL_MODE 33
#define LH_SSL_CTRL_SET_TLSEXT_HOSTNAME 55
#define LH_SSL_CTRL_SET_MIN_PROTO_VERSION 123
#define LH_TLSEXT_NAMETYPE_host_name 0
#define LH_TLS1_2_VERSION 0x0303
#define LH_SSL_MODE_RELEASE_BUFFERS 0x00000010U

#define LH_SSL_VERIFY_PEER 0x01

#define LH_X509_V_OK 0
#define LH_X509_V_FLAG_PARTIAL_CHAIN 0x80000
#define LH_X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS 0x4
#define LH_X509_CHECK_FLAG_NEVER_CHECK_SUBJECT 0x20

#define LH_SSL_ERROR_NONE 0
#define LH_SSL_ERROR_SSL 1
#define LH_SSL_ERROR_WANT_READ 2
#define LH_SSL_ERROR_WANT_WRITE 3
#define LH_SSL_ERROR_SYSCALL 5
#define LH_SSL_ERROR_ZERO_RETURN 6

#define LH_SSL_SENT_SHUTDOWN 1
#define LH_SSL_RECEIVED_SHUTDOWN 2

#define LH_BIO_CTRL_PENDING 10
#define LH_BIO_C_SET_BUF_MEM_EOF_RETURN 130

#endif
