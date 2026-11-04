#!/usr/bin/env python3
"""Seeded inputs for scripts/diff.sh: the same seed gives the same bytes on every machine.

Only random.Random(seed).getrandbits is used: Python guarantees the core generator's sequence
across versions, but not the algorithms behind randrange, choice or shuffle.

Usage: inputs.py smoke SEED   one u32 slice per line, 20 slices for each length 0..64
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


def main() -> int:
    if len(sys.argv) != 3 or sys.argv[1] != "smoke":
        print("usage: inputs.py smoke SEED", file=sys.stderr)
        return 2
    smoke(int(sys.argv[2]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
