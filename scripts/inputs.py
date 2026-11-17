#!/usr/bin/env python3
"""Seeded inputs for scripts/diff.sh: the same seed gives the same bytes on every machine.

Only random.Random(seed).getrandbits is used: Python guarantees the core generator's sequence
across versions, but not the algorithms behind randrange, choice or shuffle.

Usage: inputs.py smoke SEED   one u32 slice per line, 20 slices for each length 0..64
       inputs.py adder SEED   one case per line for the adder evaluators (rust/adder/src/bin/adder_eval.rs):
                              `bits <a> <b> <sum>` and `u64 <a> <b>`
"""

import random
import sys

U32_MAX = 2**32 - 1


def smoke(seed: int) -> None:
    rng = random.Random(seed)
    for length in range(65):
        for _ in range(20):
            kind = rng.getrandbits(2)
            if kind == 0:  # all zeros
                values = [0] * length
            elif kind == 1:  # small values: no overflow below length 64
                values = [rng.getrandbits(32) % 1000 for _ in range(length)]
            elif kind == 2:  # near the maximum: overflows from length 2 on
                values = [U32_MAX - rng.getrandbits(16) for _ in range(length)]
            else:  # full range
                values = [rng.getrandbits(32) for _ in range(length)]
            print(" ".join(map(str, values)))


U64_MAX = 2**64 - 1


def adder(seed: int) -> None:
    rng = random.Random(seed)

    def show(n: int, value: int) -> str:
        """The low n bits of value, least significant first; `-` is the empty string."""
        return "".join("1" if (value >> i) & 1 else "0" for i in range(n)) or "-"

    def pair(n: int) -> tuple[int, int]:
        mask = (1 << n) - 1
        kind = rng.getrandbits(2)
        if kind == 0:  # no carry anywhere: the two numbers share no set bit
            a = rng.getrandbits(n) if n else 0
            return a, (rng.getrandbits(n) if n else 0) & ~a & mask
        if kind == 1:  # the longest carry chain: all ones plus a low bit
            return mask, 1 & mask
        if kind == 2:  # complementary bits, then plus one: the carry runs to the top
            a = rng.getrandbits(n) if n else 0
            return a, ((~a & mask) + 1) & mask
        return (rng.getrandbits(n) if n else 0), (rng.getrandbits(n) if n else 0)

    # add_bits with a sum buffer of the right length: 20 cases for each length 0..64, then 5
    # cases for each of a few longer lengths. The buffer starts with random contents. The
    # lengths stop at 1000 because the native evaluator of the translation slows down fast:
    # 0.26 s for one case of length 511, 1.0 s at 1000, 8.5 s at 2000 (measured 2026-11-17).
    for n in list(range(65)) * 20 + [100, 127, 128, 255, 256, 511, 1000] * 5:
        a, b = pair(n)
        print("bits", show(n, a), show(n, b), show(n, rng.getrandbits(n) if n else 0))
    # add_bits with a sum buffer of the wrong length: the call returns None and leaves it alone.
    for _ in range(200):
        n, m = rng.getrandbits(6), rng.getrandbits(6)
        if m == n:
            m = n + 1
        a, b = pair(n)
        print("bits", show(n, a), show(n, b), show(m, rng.getrandbits(m) if m else 0))
    # add_u64: every pair of edge values, then random pairs, half of them next to the carry
    # boundary a + b = 2^64.
    edges = [0, 1, 2, 3, U64_MAX, U64_MAX - 1, 1 << 63, (1 << 63) - 1, 0x5555555555555555, 0xAAAAAAAAAAAAAAAA]
    for a in edges:
        for b in edges:
            print("u64", a, b)
    for _ in range(1900):
        a = rng.getrandbits(64)
        kind = rng.getrandbits(2)
        if kind == 0:  # a + b = 2^64 - 1: the largest sum without a carry
            b = U64_MAX - a
        elif kind == 1:  # a + b = 2^64: the smallest sum with a carry
            b = (U64_MAX - a + 1) & U64_MAX
        else:
            b = rng.getrandbits(64)
        print("u64", a, b)


GENERATORS = {"smoke": smoke, "adder": adder}


def main() -> int:
    if len(sys.argv) != 3 or sys.argv[1] not in GENERATORS:
        print(f"usage: inputs.py {'|'.join(GENERATORS)} SEED", file=sys.stderr)
        return 2
    GENERATORS[sys.argv[1]](int(sys.argv[2]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
