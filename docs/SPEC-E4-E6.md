# Frozen Interface Contract: Gates E4, E5, and E6 (`general_engine`)

Base commit: `e5c753d21bfdaa155eec919c254926f96dae95ff` (`vizier/engine-weights-input-20261118`).
Target: generalize `rust/engine` (1-layer, 3-token mod-113) into a proved multi-layer causal integer language model engine (`rust/general_engine`), train and quantize a real 2-layer byte-level LM checkpoint that passes `load_check`, and serve that exact proved Rust crate in WebAssembly in a local browser page.

## 1. Fixed Architecture Constants (`rust/general_engine/src/lib.rs`)

- `#![no_std]`, `#![forbid(unsafe_code)]`, `overflow-checks = true` in `[profile.dev]` and `[profile.release]`.
- `pub const MAX_LAYERS: usize = 2;`
- `pub const VOCAB: usize = 256;`
- `pub const MAX_SEQ: usize = 32;`
- `pub const D_MODEL: usize = 128;`
- `pub const N_HEADS: usize = 4;`
- `pub const D_HEAD: usize = 32;`
- `pub const D_MLP: usize = 512;`
- `pub const EXP_ONE: i64 = 1 << 30;`
- `pub const EXP_FRAC_BITS: u32 = 30;`
- `pub const EXP_N_LEN: i64 = 32;`
- `pub const ALPHA_ONE: i64 = 1 << 24;`

## 2. Exact `LayerWeights` and `Weights` Structs

```rust
pub struct LayerWeights {
    pub wq: [[[i8; D_HEAD]; D_MODEL]; N_HEADS],
    pub wk: [[[i8; D_HEAD]; D_MODEL]; N_HEADS],
    pub wv: [[[i8; D_HEAD]; D_MODEL]; N_HEADS],
    pub wo: [[[i8; D_MODEL]; D_HEAD]; N_HEADS],
    pub win: [[i8; D_MLP]; D_MODEL],
    pub bin: [i64; D_MLP],
    pub wout: [[i8; D_MODEL]; D_MLP],
    pub bout: [i64; D_MODEL],
}

pub struct Weights {
    pub n_layers: usize,   // valid iff 1 <= n_layers && n_layers <= MAX_LAYERS
    pub vocab_size: usize, // valid iff 1 <= vocab_size && vocab_size <= VOCAB
    pub tok: [[i8; D_MODEL]; VOCAB],
    pub pos: [[i8; D_MODEL]; MAX_SEQ],
    pub layers: [LayerWeights; MAX_LAYERS],
    pub u: [[i8; VOCAB]; D_MODEL],
    pub exp_n: [i64; 32],
    pub exp_2: [i64; 256],
    pub exp_1: [i64; 256],
    pub exp_0: [i64; 256],
}
```

## 3. `load_check(w: &Weights) -> bool`

Returns `true` iff ALL of the following hold (using explicit `while` loops so Charon + Aeneas translate cleanly):
- `w.n_layers >= 1 && w.n_layers <= MAX_LAYERS`
- `w.vocab_size >= 1 && w.vocab_size <= VOCAB`
- Every `tok[t][k]` in `[-68, 68]` (`0 <= t < VOCAB`), every `pos[p][k]` in `[-59, 59]` (`0 <= p < MAX_SEQ`)
- For each `l` in `0..MAX_LAYERS`:
  - `wq[h][i][j]` in `[-5, 5]`, `wk[h][i][j]` in `[-22, 22]`, `wv[h][i][j]` in `[-106, 106]`, `wo[h][j][i]` in `[-93, 93]`
  - `win[i][m]` in `[-82, 82]`, `wout[m][i]` in `[-74, 74]`
  - `bin[m]` in `[-(1 << 30), 1 << 30]`, `bout[i]` in `[-(1 << 37), 1 << 37]`
- Every `u[i][v]` in `[-37, 37]` (`0 <= i < D_MODEL, 0 <= v < VOCAB`)
- Every entry of `exp_n`, `exp_2`, `exp_1`, `exp_0` in `[0, EXP_ONE]`

## 4. Exact Forward Semantics (Causal Multi-Layer + Exact Mod-113 Compatibility)

Inputs to `forward_logits(w: &Weights, tokens: &[usize; MAX_SEQ], seq_len: usize) -> Option<[i64; VOCAB]>` and `predict_next(w: &Weights, tokens: &[usize; MAX_SEQ], seq_len: usize) -> Option<usize>`:
1. Guard: if `seq_len == 0 || seq_len > MAX_SEQ` return `None`. If `w.n_layers == 0 || w.n_layers > MAX_LAYERS || w.vocab_size == 0 || w.vocab_size > VOCAB` return `None`. Check `tokens[p] < VOCAB` for all `0 <= p < seq_len`; if any `tokens[p] >= VOCAB`, return `None`.
2. Initial stream `x[p][k]` (`0 <= p < seq_len`): `w.tok[tokens[p]][k] as i64 + w.pos[p][k] as i64` (for `p >= seq_len`, `0`). Every active row satisfies `|x[p][k]| <= 127`.
3. Layer loop `l = 0; while l < w.n_layers`:
   - For each active position `p` in `0..seq_len`:
     - Causal attention at position `p` attends ONLY over `j` in `0..=p`:
       - `q = project(&x[p], &layer.wq[h])`
       - For `j` in `0..=p`: `scores[j] = dot(&q, &project(&x[j], &layer.wk[h]))`
       - `max_s = max_{0 <= j <= p} scores[j]`
       - For `j` in `0..=p`: `e[j] = exp_fix(w, max_s - scores[j])`; `denom = sum_{0 <= j <= p} e[j]` (guaranteed `>= EXP_ONE` because `max_s - scores[j_max] == 0 => exp_fix == EXP_ONE`)
       - For `j` in `0..=p`: `alpha[j] = (e[j] * ALPHA_ONE) / denom` (Rust signed integer `/` truncates toward zero = Lean `Int.tdiv`, sum `<= ALPHA_ONE`)
       - `mixed[d] = (sum_{0 <= j <= p} alpha[j] * v_j[d]) >> 16`
       - `head_out` via `layer.wo[h]`, summed across `4` heads -> `att[k]`
     - `r = residual(&x[p], &att)` (`x[p][k] * ALPHA_ONE + att[k]`)
     - `m = mlp_hidden(layer, &r)` (`(lincomb + bin * 256)`, `<= 0 -> 0`, `> 0 -> >> 8`)
     - `o = mlp_output(layer, &m)` (`lincomb + bout`)
     - `f = final_stream(&r, &o)` (`(r[k] * 256 + o[k]) >> 16`, at scale `2^24`)
     - **Inter-layer rescale:** if `l + 1 < w.n_layers`, rescale `f` back to scale `2^8` and clamp to `[-127, 127]`:
       `let s = f[k] >> 16; x_next[p][k] = if s < -127 { -127 } else if s > 127 { 127 } else { s };`
       If `l + 1 == w.n_layers` (final active layer), keep `last_hidden = f` at `p = seq_len - 1` (at scale `2^24`, matching `rust/engine`).
4. Unembed `last_hidden` (`p = seq_len - 1`) with `w.u`: `logits[v] = sum_{k=0..128} last_hidden[k] * (w.u[k][v] as i64)` for `v` in `0..VOCAB`.
5. `predict_next` picks strict `>` first-maximum index over `0..w.vocab_size`.
6. `generate_greedy(w: &Weights, buf: &mut [usize; MAX_SEQ], prompt_len: usize, steps: usize) -> Option<usize>`: appends up to `steps` predicted tokens while `cur_len < MAX_SEQ`, returning final length.

**Mod-113 Equivalence:** When `w.n_layers == 1`, `w.vocab_size == 113`, `seq_len == 3`, `tokens[0..3] = [a, b, 113]`, position `p = 2` attends over `j in 0..=2` with zero inter-layer clamp, unembeds with `u[..][0..113]`, and picks strict-`>` argmax over `0..113`, matching `rust/engine::predict` bit-for-bit on all 12,769 pairs.

## 5. Binary Weight File Format (`GLMW` v1, exact 479,504 bytes)

Little-endian packed binary file (`weights/tiny_bytelm_v1.bin` and `weights/mod113_v1.bin`) so Python, native Rust, and browser Wasm load identical bytes:
1. Magic: `b"GLMW"` (4 bytes)
2. Version: `u32` LE = `1` (4 bytes)
3. `n_layers`: `u32` LE (4 bytes)
4. `vocab_size`: `u32` LE (4 bytes)
5. `tok`: `256 * 128` signed `i8` bytes (32,768 B)
6. `pos`: `32 * 128` signed `i8` bytes (4,096 B)
7. For `l = 0, 1` (`MAX_LAYERS = 2`):
   - `wq`: `4 * 128 * 32` `i8` (16,384 B)
   - `wk`: `4 * 128 * 32` `i8` (16,384 B)
   - `wv`: `4 * 128 * 32` `i8` (16,384 B)
   - `wo`: `4 * 32 * 128` `i8` (16,384 B)
   - `win`: `128 * 512` `i8` (65,536 B)
   - `bin`: `512` `i64` LE (4,096 B)
   - `wout`: `512 * 128` `i8` (65,536 B)
   - `bout`: `128` `i64` LE (1,024 B)
   (Each layer = 201,728 B; 2 layers = 403,456 B)
8. `u`: `128 * 256` `i8` (32,768 B)
9. `exp_n`: `32` `i64` LE (256 B)
10. `exp_2`: `256` `i64` LE (2,048 B)
11. `exp_1`: `256` `i64` LE (2,048 B)
12. `exp_0`: `256` `i64` LE (2,048 B)

Total exact file size: `479,504` bytes.
