/*
 * JARDIN-Keccak-128-24 one-shot CLI.
 *
 *   Usage:  jardin-keccak-128-24 <seed_48B_hex> <message_hex>                     # hedged (default)
 *           jardin-keccak-128-24 <seed_48B_hex> <message_hex> <optrand_16B_hex>   # explicit opt_rand
 *
 * `seed_48B` = sk_seed(16) || sk_prf(16) || pk_seed(16) — pass whatever
 * derivation you like from the outside.
 *
 * **Default is hedged** (FIPS 205 §9.2 recommendation). The per-signature
 * randomizer (`opt_rand`) is drawn from the kernel CSPRNG (getrandom(2),
 * fallback /dev/urandom). The actual `opt_rand` bytes used are printed to
 * stderr so a hedged sig can be reproduced exactly via the deterministic
 * interface if needed.
 *
 * Pass a 16-byte hex `opt_rand` as the third positional arg to force a
 * specific randomizer (deterministic mode — only useful for KATs).
 *
 * Output to stdout (one line, hex, no 0x):
 *   pk_seed(16) || pk_root(16) || sig(SPX_BYTES = 3856)
 *
 *   = 32 + 3856 = 3888 bytes = 7776 hex chars.
 *
 * Exit status 0 on success, non-zero on usage or internal error.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

#include "params.h"
#include "api.h"
#include "randombytes.h"

#ifdef __linux__
#include <sys/random.h>
#endif

/* set_rng_buffer is declared here (not in randombytes.h) because it's an
   internal hook for this harness only, not part of the SPHINCS+ API. */
extern void set_rng_buffer(const unsigned char *buf, unsigned long long len);

static int hex_nibble(int c)
{
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

static int hex_decode(const char *hex, unsigned char *out, size_t out_len)
{
    size_t hlen = strlen(hex);
    if (hlen >= 2 && hex[0] == '0' && (hex[1] == 'x' || hex[1] == 'X')) {
        hex += 2;
        hlen -= 2;
    }
    if (hlen != out_len * 2) return -1;
    for (size_t i = 0; i < out_len; i++) {
        int hi = hex_nibble(hex[2 * i]);
        int lo = hex_nibble(hex[2 * i + 1]);
        if (hi < 0 || lo < 0) return -1;
        out[i] = (unsigned char)((hi << 4) | lo);
    }
    return 0;
}

static void hex_print(const unsigned char *buf, size_t len)
{
    for (size_t i = 0; i < len; i++) printf("%02x", buf[i]);
    putchar('\n');
}

/* Fill `out` with `len` cryptographically secure random bytes. Returns 0 on
 * success, -1 on failure. Tries getrandom(2) first, falls back to /dev/urandom. */
static int csprng_fill(unsigned char *out, size_t len)
{
#ifdef __linux__
    size_t got = 0;
    while (got < len) {
        ssize_t n = getrandom(out + got, len - got, 0);
        if (n < 0) {
            if (errno == EINTR) continue;
            break;
        }
        got += (size_t) n;
    }
    if (got == len) return 0;
#endif
    FILE *f = fopen("/dev/urandom", "rb");
    if (!f) return -1;
    size_t n = fread(out, 1, len, f);
    fclose(f);
    return (n == len) ? 0 : -1;
}

int main(int argc, char **argv)
{
    int hedged = 0;
    const char *seed_hex = NULL;
    const char *msg_hex_arg = NULL;
    const char *optrand_hex = NULL;

    if (argc == 3) {
        /* New default: hedged. */
        hedged      = 1;
        seed_hex    = argv[1];
        msg_hex_arg = argv[2];
    } else if (argc == 4 && strcmp(argv[1], "--hedged") == 0) {
        /* Backwards-compat. */
        hedged      = 1;
        seed_hex    = argv[2];
        msg_hex_arg = argv[3];
    } else if (argc == 4) {
        /* Deterministic mode. */
        seed_hex    = argv[1];
        msg_hex_arg = argv[2];
        optrand_hex = argv[3];
    } else {
        fprintf(stderr,
            "Usage:\n"
            "  %s <seed_48B_hex> <message_hex>                     (HEDGED, default — opt_rand from kernel CSPRNG)\n"
            "  %s <seed_48B_hex> <message_hex> <optrand_16B_hex>   (explicit opt_rand — for KATs)\n"
            "  seed = sk_seed(16) || sk_prf(16) || pk_seed(16)\n"
            "  message = arbitrary-length hex (pad nothing)\n"
            "  optrand = %d bytes (the per-sig randomizer)\n"
            "\nOutput: hex(pk_seed(16) || pk_root(16) || sig(%d))\n",
            argv[0], argv[0], SPX_N, SPX_BYTES);
        return 2;
    }

    unsigned char seed[CRYPTO_SEEDBYTES];        /* = 3 * SPX_N = 48 */
    if (hex_decode(seed_hex, seed, sizeof(seed)) != 0) {
        fprintf(stderr, "bad seed hex (need %zu bytes)\n", sizeof(seed));
        return 1;
    }

    size_t msg_hex_len = strlen(msg_hex_arg);
    if (msg_hex_len >= 2 && msg_hex_arg[0] == '0' &&
        (msg_hex_arg[1] == 'x' || msg_hex_arg[1] == 'X')) msg_hex_len -= 2;
    if (msg_hex_len & 1) {
        fprintf(stderr, "message hex must have even length\n");
        return 1;
    }
    size_t msg_len = msg_hex_len / 2;
    if (msg_len != 32) {
        fprintf(stderr, "message must be exactly 32 bytes (64 hex chars); the on-chain "
                        "convention is bytes32. got %zu bytes\n", msg_len);
        return 1;
    }
    unsigned char *msg = (unsigned char *)malloc(msg_len);
    if (!msg) { fprintf(stderr, "oom\n"); return 1; }
    if (hex_decode(msg_hex_arg, msg, msg_len) != 0) {
        fprintf(stderr, "bad message hex\n"); free(msg); return 1;
    }

    unsigned char optrand[SPX_N];
    if (hedged) {
        if (csprng_fill(optrand, sizeof(optrand)) != 0) {
            fprintf(stderr, "csprng_fill failed: no getrandom and no /dev/urandom\n");
            free(msg); return 1;
        }
        fprintf(stderr, "  mode: hedged (opt_rand=");
        for (size_t i = 0; i < sizeof(optrand); i++) fprintf(stderr, "%02x", optrand[i]);
        fprintf(stderr, ")\n");
    } else if (hex_decode(optrand_hex, optrand, sizeof(optrand)) != 0) {
        fprintf(stderr, "bad optrand hex (need %d bytes)\n", SPX_N);
        free(msg); return 1;
    }

    unsigned char pk[SPX_PK_BYTES];              /* = 32 */
    unsigned char sk[SPX_SK_BYTES];              /* = 64 */
    fprintf(stderr, "  keygen (single XMSS, 2^%d leaves)...\n", SPX_FULL_HEIGHT);
    if (crypto_sign_seed_keypair(pk, sk, seed) != 0) {
        fprintf(stderr, "keygen failed\n"); free(msg); return 1;
    }
    fprintf(stderr, "  pk_seed = "); for (int i = 0; i < 4; i++) fprintf(stderr, "%02x", pk[i]); fprintf(stderr, "...\n");
    fprintf(stderr, "  pk_root = "); for (int i = 0; i < 4; i++) fprintf(stderr, "%02x", pk[SPX_N + i]); fprintf(stderr, "...\n");

    unsigned char sig[SPX_BYTES];                /* = 3856 */
    size_t siglen = 0;
    set_rng_buffer(optrand, sizeof(optrand));
    fprintf(stderr, "  signing (FORS + XMSS)...\n");
    if (crypto_sign_signature(sig, &siglen, msg, msg_len, sk) != 0) {
        fprintf(stderr, "sign failed\n"); free(msg); return 1;
    }
    if (siglen != SPX_BYTES) {
        fprintf(stderr, "unexpected siglen %zu != %d\n", siglen, SPX_BYTES);
        free(msg); return 1;
    }
    fprintf(stderr, "  sig: %zu bytes\n", siglen);

    /* Emit pk_seed || pk_root || sig as hex. */
    unsigned char out[2 * SPX_N + SPX_BYTES];
    memcpy(out,              pk,           SPX_N);            /* pk_seed */
    memcpy(out + SPX_N,      pk + SPX_N,   SPX_N);            /* pk_root */
    memcpy(out + 2 * SPX_N,  sig,          SPX_BYTES);
    hex_print(out, sizeof(out));

    free(msg);
    return 0;
}
