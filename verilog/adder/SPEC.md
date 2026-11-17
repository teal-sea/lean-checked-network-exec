# Formally verify that the circuit `rnn_adder` is a bit-serial adder

`rnn_adder.sv` is a small trained recurrent neural network as a synchronous circuit. Its hidden
state is the 4-bit register `h`. Every cycle it reads one bit of each of two numbers on `a` and
`b`, least significant bit first. `sum` and `carry` are combinational outputs. The weights are
integers and every activation is a threshold at zero; the header comment of the file gives the
three formulas. The top module is `rnn_adder`.

## Assumptions

- `reset` is high at the first rising edge of `clk` and low at every later rising edge.
- `a` and `b` are unconstrained. They may take any value in every cycle.

## Notation

Fix any infinite input stream. Let `a[t]` and `b[t]`, for `t = 0, 1, 2, ...`, be the values of `a`
and `b` sampled at the `(t + 1)`-th rising edge after the reset edge, so `a[0]`, `b[0]` are the
first inputs sampled after reset. Define the carries of binary addition:

- `c[0] = 0`,
- `c[t + 1] = (a[t] & b[t]) | (a[t] & c[t]) | (b[t] & c[t])`.

"The state after `n` inputs" means the state of the circuit after the reset edge and `n` further
rising edges, for any `n >= 0`.

## Properties

Each property is for every `n >= 0` and every input stream.

1. **The carry.** In the state after `n` inputs, once the combinational logic has settled,
   `carry == c[n]`.

2. **The sum bit.** In the state after `n` inputs, for the values currently on `a` and `b`,
   once the combinational logic has settled, `sum == a ^ b ^ c[n]`. In particular, in the
   cycle in which `a[n]` and `b[n]` are applied, `sum == a[n] ^ b[n] ^ c[n]`.

3. **The circuit adds.** Let `s[t] = a[t] ^ b[t] ^ c[t]` be the value of `sum` in the cycle in
   which `a[t]`, `b[t]` are applied (property 2). Then for every `n`, as mathematical integers,

   `sum over t < n of s[t] * 2^t  +  c[n] * 2^n  ==  sum over t < n of a[t] * 2^t  +  sum over t < n of b[t] * 2^t`.

   That is: the `n` sum bits the circuit emitted, together with the carry it shows after them,
   are the binary sum of the two `n`-bit numbers it read.

## A hint, not an assumption

Prove this or ignore it; nothing may be assumed from it.

After the reset edge the register `h` only ever holds one of five values. Written as
`{h[3], h[2], h[1], h[0]}`: `0000`, `0111`, `1001`, `0110`, `1000`. On these `carry` is
`0, 0, 1, 0, 1` in that order. For each of the five states and each of the four input pairs, the
next state is again one of the five, the next state's `carry` is the majority of `a`, `b` and the
current `carry`, and `sum` is `a ^ b ^` the current `carry`. That is 20 finite cases, and the
invariant "the state is one of the five and `carry == c[n]`" gives properties 1 to 3 by induction
on `n`.
