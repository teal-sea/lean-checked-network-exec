# The adder in C

The recurrent adder of `RnnAdder.Network` in C11, function for function the same program as
`rust/adder/src/lib.rs`. `weights.h` is generated from `lean/RnnAdder/Trained.lean` by
`scripts/gen_adder_weights.py`, as the Rust weights are.

It exists for two Aristotle checks: memory safety of the C (gate 1B), and that the Rust and the
C return the same results on every input. Neither has been submitted.

```sh
cc -std=c11 -O2 -Wall -Wextra -fsanitize=address,undefined adder.c test_adder.c -o test_adder
./test_adder
```

`test_adder.c` checks every bit sequence of length 0 to 8 against the ripple-carry adder, the
length-mismatch return, and 64-bit addition on 100 edge pairs and 1,000,000 seeded pairs. On
2026-11-17 with cc 13.3.0 it printed `ok: 0 failures`. These are tests, not a proof.
