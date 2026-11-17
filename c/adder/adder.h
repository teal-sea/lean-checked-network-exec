/* The trained recurrent adder of RnnAdder.Network, evaluated in C.
 *
 * The same network as rust/adder/src/lib.rs, function for function. The weights in weights.h
 * are generated from lean/RnnAdder/Trained.lean by scripts/gen_adder_weights.py.
 */
#ifndef ADDER_H_INCLUDED
#define ADDER_H_INCLUDED

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "weights.h"

/* One input: the bit of the first number and the bit of the second number at one position. */
typedef struct {
    bool a;
    bool b;
} adder_bit_pair;

/* One step of the state: writes the next state to next. h and next must not overlap. */
void adder_step(const bool h[ADDER_H], bool a, bool b, bool next[ADDER_H]);

/* The sum bit emitted at a step. */
bool adder_out(const bool h[ADDER_H], bool a, bool b);

/* The carry read off a state. */
bool adder_carry(const bool h[ADDER_H]);

/* Runs the network over the n pairs of xs, least significant pair first, starting from
 * ADDER_H0. Writes one sum bit per pair into sum and returns the final carry, 0 or 1.
 * Returns -1, leaving sum unchanged, when sum_len != n. */
int adder_add_bits(const adder_bit_pair *xs, size_t n, bool *sum, size_t sum_len);

/* The network as a 64-bit adder: feeds it the 64 bit pairs of a and b, least significant
 * first, packs the 64 sum bits into the return value and stores the final carry in *carry. */
uint64_t adder_add_u64(uint64_t a, uint64_t b, bool *carry);

#endif
