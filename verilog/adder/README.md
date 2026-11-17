# The adder as a circuit

The recurrent adder of `RnnAdder.Network` in SystemVerilog: 4 flip-flops for the hidden state,
integer weights, thresholds at zero. `rnn_adder.sv` is generated from
`lean/RnnAdder/Trained.lean` by `scripts/gen_adder_weights.py`, as the Rust and C weights are.

`SPEC.md` asks Aristotle to prove it is a bit-serial adder on every input stream.

```sh
iverilog -g2012 -o tb_rnn_adder rnn_adder.sv tb_rnn_adder.sv && vvp tb_rnn_adder
```

`tb_rnn_adder.sv` compares the circuit with a reference serial adder on every input sequence of
length 0 to 7 and on 200 seeded streams of 1,000 bit pairs. On 2026-11-17 with Icarus Verilog
12.0 it printed `ok: 713317 checks, 0 errors`. This is a test, not a proof.
