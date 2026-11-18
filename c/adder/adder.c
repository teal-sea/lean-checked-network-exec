#include "adder.h"

/* Sum of the weights at the positions where the state is true. */
static int32_t dot_b(const int32_t w[ADDER_H], const bool h[ADDER_H]) {
    int32_t acc = 0;
    for (size_t i = 0; i < ADDER_H; i++) {
        if (h[i]) {
            acc += w[i];
        }
    }
    return acc;
}

/* The threshold activation. */
static bool thr(int32_t z) {
    return z > 0;
}

void adder_step(const bool h[ADDER_H], bool a, bool b, bool next[ADDER_H]) {
    for (size_t i = 0; i < ADDER_H; i++) {
        int32_t z = dot_b(ADDER_WH[i], h);
        if (a) {
            z += ADDER_WXA[i];
        }
        if (b) {
            z += ADDER_WXB[i];
        }
        z += ADDER_BH[i];
        next[i] = thr(z);
    }
}

bool adder_out(const bool h[ADDER_H], bool a, bool b) {
    bool next[ADDER_H];
    adder_step(h, a, b, next);
    int32_t z = dot_b(ADDER_WO, next);
    if (a) {
        z += ADDER_WOA;
    }
    if (b) {
        z += ADDER_WOB;
    }
    z += ADDER_BO;
    return thr(z);
}

bool adder_carry(const bool h[ADDER_H]) {
    return thr(dot_b(ADDER_WC, h) + ADDER_BC);
}

int adder_add_bits(const adder_bit_pair *xs, size_t n, bool *sum, size_t sum_len) {
    if (sum_len != n) {
        return -1;
    }
    bool h[ADDER_H];
    for (size_t k = 0; k < ADDER_H; k++) {
        h[k] = ADDER_H0[k];
    }
    for (size_t i = 0; i < n; i++) {
        bool a = xs[i].a;
        bool b = xs[i].b;
        bool next[ADDER_H];
        sum[i] = adder_out(h, a, b);
        adder_step(h, a, b, next);
        for (size_t k = 0; k < ADDER_H; k++) {
            h[k] = next[k];
        }
    }
    return adder_carry(h) ? 1 : 0;
}

uint64_t adder_add_u64(uint64_t a, uint64_t b, bool *carry) {
    bool h[ADDER_H];
    for (size_t k = 0; k < ADDER_H; k++) {
        h[k] = ADDER_H0[k];
    }
    uint64_t s = 0;
    for (unsigned i = 0; i < 64; i++) {
        bool abit = ((a >> i) & 1u) == 1u;
        bool bbit = ((b >> i) & 1u) == 1u;
        bool next[ADDER_H];
        if (adder_out(h, abit, bbit)) {
            s |= (uint64_t)1 << i;
        }
        adder_step(h, abit, bbit, next);
        for (size_t k = 0; k < ADDER_H; k++) {
            h[k] = next[k];
        }
    }
    *carry = adder_carry(h);
    return s;
}
