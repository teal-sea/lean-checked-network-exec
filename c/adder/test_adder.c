/* Tests of the C adder against ordinary integer addition. These are tests, not the proof.
 *
 *   cc -std=c11 -O2 -Wall -Wextra -fsanitize=address,undefined adder.c test_adder.c -o test_adder
 *   ./test_adder
 */
#include <stdio.h>
#include <stdlib.h>

#include "adder.h"

static uint64_t state = 2;

/* SplitMix64, the generator rust/adder/tests/adds.rs uses. */
static uint64_t next_u64(void) {
    state += 0x9E3779B97F4A7C15ull;
    uint64_t z = state;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
    return z ^ (z >> 31);
}

static int check_u64(uint64_t a, uint64_t b) {
    bool carry = false;
    uint64_t s = adder_add_u64(a, b, &carry);
    uint64_t want = a + b;
    bool want_carry = want < a;
    if (s != want || carry != want_carry) {
        printf("FAIL add_u64(%llu, %llu)\n", (unsigned long long)a, (unsigned long long)b);
        return 1;
    }
    return 0;
}

int main(void) {
    int bad = 0;

    /* Every sequence of length 0 to 8 against the ripple-carry adder. */
    for (size_t n = 0; n <= 8; n++) {
        for (uint32_t code = 0; code < (1u << (2 * n)); code++) {
            adder_bit_pair xs[8];
            bool sum[8];
            bool c = false;
            int ok = 1;
            for (size_t i = 0; i < n; i++) {
                xs[i].a = (code >> (2 * i)) & 1u;
                xs[i].b = (code >> (2 * i + 1)) & 1u;
            }
            int got = adder_add_bits(xs, n, sum, n);
            for (size_t i = 0; i < n; i++) {
                bool want = xs[i].a ^ xs[i].b ^ c;
                c = (xs[i].a && xs[i].b) || (xs[i].a && c) || (xs[i].b && c);
                if (sum[i] != want) {
                    ok = 0;
                }
            }
            if (!ok || got != (c ? 1 : 0)) {
                printf("FAIL add_bits length %zu code %u\n", n, code);
                bad++;
            }
        }
    }

    /* Length mismatch. */
    {
        adder_bit_pair xs[3] = {{true, true}, {true, true}, {true, true}};
        bool sum[2] = {true, false};
        if (adder_add_bits(xs, 3, sum, 2) != -1 || sum[0] != true || sum[1] != false) {
            printf("FAIL length mismatch\n");
            bad++;
        }
    }

    /* 64-bit addition: edges, then a million seeded pairs. */
    const uint64_t edges[] = {0, 1, 2, 3, UINT64_MAX, UINT64_MAX - 1, 1ull << 63, (1ull << 63) - 1,
                              0x5555555555555555ull, 0xAAAAAAAAAAAAAAAAull};
    for (size_t i = 0; i < sizeof edges / sizeof edges[0]; i++) {
        for (size_t j = 0; j < sizeof edges / sizeof edges[0]; j++) {
            bad += check_u64(edges[i], edges[j]);
        }
    }
    for (int i = 0; i < 1000000; i++) {
        uint64_t a = next_u64();
        uint64_t b = next_u64();
        bad += check_u64(a, b);
    }

    printf("%s: %d failures\n", bad ? "FAIL" : "ok", bad);
    return bad ? EXIT_FAILURE : EXIT_SUCCESS;
}
