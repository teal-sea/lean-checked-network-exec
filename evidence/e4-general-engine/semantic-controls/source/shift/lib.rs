//! Runtime-weights multi-layer causal integer transformer engine.
//! Call `load_check` once before evaluation. Generalizes `rust/engine` (one layer, three
//! positions, mod 113) to `n_layers <= 2` layers over `seq_len <= 32` causal positions with a
//! `vocab_size <= 256` output head. Arithmetic, shifts and tie-breaking follow
//! `docs/SPEC-E4-E6.md` and agree bit-for-bit with `rust/engine` in the mod-113
//! configuration (`n_layers = 1`, `vocab_size = 113`, `seq_len = 3`).
#![no_std]
#![forbid(unsafe_code)]

pub const MAX_LAYERS: usize = 2;
pub const VOCAB: usize = 256;
pub const MAX_SEQ: usize = 32;
pub const D_MODEL: usize = 128;
pub const N_HEADS: usize = 4;
pub const D_HEAD: usize = 32;
pub const D_MLP: usize = 512;
pub const EXP_ONE: i64 = 1 << 30;
pub const EXP_FRAC_BITS: u32 = 30;
pub const EXP_N_LEN: i64 = 32;
/// A softmax weight of 1, scale 2^24.
pub const ALPHA_ONE: i64 = 1 << 24;

/// One transformer layer. Fixed dimensions enforce every shape requirement at the Rust type
/// boundary.
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

/// Weights for the whole engine. `layers[0..n_layers]` are active; the remaining layers are
/// padding and only participate in `load_check`. `tok` and `u` cover the full 256-token
/// vocabulary so sibling consumers (byte-level LM checkpoint, Wasm UI) share one layout.
pub struct Weights {
    pub n_layers: usize,
    pub vocab_size: usize,
    pub tok: [[i8; D_MODEL]; VOCAB],
    pub pos: [[i8; D_MODEL]; MAX_SEQ],
    pub layers: [LayerWeights; MAX_LAYERS],
    pub u: [[i8; VOCAB]; D_MODEL],
    pub exp_n: [i64; 32],
    pub exp_2: [i64; 256],
    pub exp_1: [i64; 256],
    pub exp_0: [i64; 256],
}

/// The numeric inner loop used by the attention scores.
pub fn dot(x: &[i64; D_HEAD], y: &[i64; D_HEAD]) -> i64 {
    let mut acc = 0i64;
    let mut i = 0;
    while i < D_HEAD {
        acc += x[i] * y[i];
        i += 1;
    }
    acc
}

fn bounded_i8<const N: usize>(xs: &[i8; N], limit: i8) -> bool {
    let mut i = 0;
    while i < N {
        if xs[i] < -limit || xs[i] > limit {
            return false;
        }
        i += 1;
    }
    true
}
fn bounded_i64<const N: usize>(xs: &[i64; N], limit: i64) -> bool {
    let mut i = 0;
    while i < N {
        if xs[i] < -limit || xs[i] > limit {
            return false;
        }
        i += 1;
    }
    true
}
fn table<const N: usize>(xs: &[i64; N]) -> bool {
    let mut i = 0;
    while i < N {
        if xs[i] < 0 || xs[i] > EXP_ONE {
            return false;
        }
        i += 1;
    }
    true
}

/// The bounds check of one layer, exactly `rust/engine::load_check`'s per-matrix shape.
fn layer_load_check(layer: &LayerWeights) -> bool {
    let mut valid = true;
    let mut h = 0;
    while h < N_HEADS {
        let mut i = 0;
        while i < D_MODEL {
            if !bounded_i8(&layer.wq[h][i], 5) || !bounded_i8(&layer.wk[h][i], 22)
                || !bounded_i8(&layer.wv[h][i], 106) {
                valid = false;
            }
            i += 1;
        }
        i = 0;
        while i < D_HEAD {
            if !bounded_i8(&layer.wo[h][i], 93) {
                valid = false;
            }
            i += 1;
        }
        h += 1;
    }
    let mut i = 0;
    while i < D_MODEL {
        if !bounded_i8(&layer.win[i], 82) {
            valid = false;
        }
        i += 1;
    }
    i = 0;
    while i < D_MLP {
        if !bounded_i8(&layer.wout[i], 74) {
            valid = false;
        }
        i += 1;
    }
    valid
        && bounded_i64(&layer.bin, 1 << 30)
        && bounded_i64(&layer.bout, 1 << 37)
}

/// Sufficient, not necessary, magnitude bounds, generalizing `rust/engine::load_check` from
/// `docs/SPEC-E4-E6.md` §3. Every stored entry of every layer, including padding layers, is
/// checked. Tables may be arbitrary in `[0, 2^30]`: the maximal score uses
/// `exp_fix(0) = 2^30` independently of table entries.
pub fn load_check(w: &Weights) -> bool {
    let mut valid = w.n_layers >= 1 && w.n_layers <= MAX_LAYERS
        && w.vocab_size >= 1 && w.vocab_size <= VOCAB;
    let mut i = 0;
    while i < VOCAB {
        if !bounded_i8(&w.tok[i], 68) {
            valid = false;
        }
        i += 1;
    }
    i = 0;
    while i < MAX_SEQ {
        if !bounded_i8(&w.pos[i], 59) {
            valid = false;
        }
        i += 1;
    }
    let mut l = 0;
    while l < MAX_LAYERS {
        if !layer_load_check(&w.layers[l]) {
            valid = false;
        }
        l += 1;
    }
    i = 0;
    while i < D_MODEL {
        if !bounded_i8(&w.u[i], 37) {
            valid = false;
        }
        i += 1;
    }
    valid
        && table(&w.exp_n)
        && table(&w.exp_2)
        && table(&w.exp_1)
        && table(&w.exp_0)
}

/// Token plus position embedding, scale 2^8. Needs `tok < 256` and `pos < 32`.
pub fn embed(w: &Weights, tok: usize, pos: usize) -> [i64; D_MODEL] {
    let mut x = [0i64; D_MODEL];
    let mut k = 0;
    while k < D_MODEL {
        x[k] = w.tok[tok][k] as i64 + w.pos[pos][k] as i64;
        k += 1;
    }
    x
}

/// The causal initial stream: `x[p]` is the embedding of `tokens[p]` at position `p` for
/// `p < seq_len`, and zero after. Needs `p < 32`, `tokens[p] < 256` for `p < seq_len`.
pub fn embed_all(w: &Weights, tokens: &[usize; MAX_SEQ], seq_len: usize) -> [[i64; D_MODEL]; MAX_SEQ] {
    let mut x = [[0i64; D_MODEL]; MAX_SEQ];
    let mut p = 0;
    while p < seq_len {
        let row = embed(w, tokens[p], p);
        x[p] = row;
        p += 1;
    }
    x
}

/// A copy of row `p` of a stream. Needs `p < 32`.
pub fn row_at(x: &[[i64; D_MODEL]; MAX_SEQ], p: usize) -> [i64; D_MODEL] {
    let mut r = [0i64; D_MODEL];
    let mut k = 0;
    while k < D_MODEL {
        r[k] = x[p][k];
        k += 1;
    }
    r
}

/// A stream vector times a 128 by 32 matrix: `out[i] = sum over k of x[k] * w[k][i]`.
/// Used for the query, key and value vectors, scale 2^16.
pub fn project(x: &[i64; D_MODEL], w: &[[i8; D_HEAD]; D_MODEL]) -> [i64; D_HEAD] {
    let mut out = [0i64; D_HEAD];
    let mut i = 0;
    while i < D_HEAD {
        let mut acc = 0i64;
        let mut k = 0;
        while k < D_MODEL {
            acc += x[k] * (w[k][i] as i64);
            k += 1;
        }
        out[i] = acc;
        i += 1;
    }
    out
}

/// Integer stand-in for `2^30 * exp(-d / 2^32)`, for `d >= 0`.
///
/// `d` is cut to 24 fractional bits, `u = d >> 8`, and split as
/// `u = n * 2^24 + b2 * 2^16 + b1 * 2^8 + b0`. The result is the product of the four table
/// entries `w.exp_n[n]`, `w.exp_2[b2]`, `w.exp_1[b1]`, `w.exp_0[b0]`, with a shift by 30
/// after each multiplication. It is `2^30` at `d = 0` and `0` when `n >= 32`. A negative `d`
/// does not occur in this program and gives `2^30`.
pub fn exp_fix(w: &Weights, d: i64) -> i64 {
    if d <= 0 {
        return EXP_ONE;
    }
    let u = d >> 8;
    let n = u >> 24;
    if n >= EXP_N_LEN {
        return 0;
    }
    let b2 = (u >> 16) & 255;
    let b1 = (u >> 8) & 255;
    let b0 = u & 255;
    let mut e = w.exp_n[n as usize];
    e = (e * w.exp_2[b2 as usize]) >> EXP_FRAC_BITS;
    e = (e * w.exp_1[b1 as usize]) >> EXP_FRAC_BITS;
    e = (e * w.exp_0[b0 as usize]) >> EXP_FRAC_BITS;
    e
}

/// The causal attention scores of head `h` of layer `l`, read at position `p`, scale 2^32:
/// `s[j] = (x[p] * wq[h]) . (x[j] * wk[h])` for `j <= p`, and `0` after. Needs `l < 2`,
/// `h < 4`, `p < 32`.
pub fn head_scores_at(w: &Weights, l: usize, h: usize, x: &[[i64; D_MODEL]; MAX_SEQ], p: usize) -> [i64; MAX_SEQ] {
    let q = project(&row_at(x, p), &w.layers[l].wq[h]);
    let mut s = [0i64; MAX_SEQ];
    let mut j = 0;
    while j <= p {
        let key = project(&row_at(x, j), &w.layers[l].wk[h]);
        s[j] = dot(&q, &key);
        j += 1;
    }
    s
}

/// The causal softmax of the scores at position `p`, scale 2^24:
/// `alpha[j] = e[j] * 2^24 / (sum_{j' <= p} e[j'])` with `e[j] = exp_fix(w, smax - s[j])`.
/// The largest score has `e = 2^30`, so the denominator is at least `2^30`. Entries after
/// `p` are `0`. Needs `p < 32`.
pub fn softmax_at(w: &Weights, s: &[i64; MAX_SEQ], p: usize) -> [i64; MAX_SEQ] {
    let mut smax = s[0];
    let mut j = 1;
    while j <= p {
        if s[j] > smax {
            smax = s[j];
        }
        j += 1;
    }
    let mut e = [0i64; MAX_SEQ];
    let mut den = 0i64;
    j = 0;
    while j <= p {
        e[j] = exp_fix(w, smax - s[j]);
        den += e[j];
        j += 1;
    }
    let mut alpha = [0i64; MAX_SEQ];
    j = 0;
    while j <= p {
        alpha[j] = (e[j] * ALPHA_ONE) / den;
        j += 1;
    }
    alpha
}

/// What head `h` of layer `l` adds to the residual stream at position `p`, scale 2^32. The
/// value vectors `x[j] * wv[h]` (scale 2^16) for `j <= p` are mixed with the softmax weights
/// (scale 2^24), shifted down to scale 2^24, and multiplied by `wo[h]`. Needs `l < 2`,
/// `h < 4`, `p < 32`.
pub fn head_out_at(w: &Weights, l: usize, h: usize, x: &[[i64; D_MODEL]; MAX_SEQ], p: usize, alpha: &[i64; MAX_SEQ]) -> [i64; D_MODEL] {
    let mut vs = [[0i64; D_HEAD]; MAX_SEQ];
    let mut j = 0;
    while j <= p {
        let v = project(&row_at(x, j), &w.layers[l].wv[h]);
        let mut i = 0;
        while i < D_HEAD {
            vs[j][i] = v[i];
            i += 1;
        }
        j += 1;
    }
    let mut z = [0i64; D_HEAD];
    let mut i = 0;
    while i < D_HEAD {
        let mut acc = 0i64;
        let mut jj = 0;
        while jj <= p {
            acc += alpha[jj] * vs[jj][i];
            jj += 1;
        }
        z[i] = acc >> 16;
        i += 1;
    }
    let mut out = [0i64; D_MODEL];
    let mut k = 0;
    while k < D_MODEL {
        let mut acc = 0i64;
        let mut t = 0;
        while t < D_HEAD {
            acc += z[t] * (w.layers[l].wo[h][t][k] as i64);
            t += 1;
        }
        out[k] = acc;
        k += 1;
    }
    out
}

/// The sum of the four heads' outputs at position `p`, scale 2^32. Needs `l < 2`, `p < 32`.
pub fn attention_at(w: &Weights, l: usize, x: &[[i64; D_MODEL]; MAX_SEQ], p: usize) -> [i64; D_MODEL] {
    let mut att = [0i64; D_MODEL];
    let mut h = 0;
    while h < N_HEADS {
        let s = head_scores_at(w, l, h, x, p);
        let alpha = softmax_at(w, &s, p);
        let ho = head_out_at(w, l, h, x, p, &alpha);
        let mut k = 0;
        while k < D_MODEL {
            att[k] += ho[k];
            k += 1;
        }
        h += 1;
    }
    att
}

/// The residual stream after attention, scale 2^32: `x_p * 2^24 + att`.
pub fn residual(x: &[i64; D_MODEL], att: &[i64; D_MODEL]) -> [i64; D_MODEL] {
    let mut r = [0i64; D_MODEL];
    let mut k = 0;
    while k < D_MODEL {
        r[k] = x[k] * ALPHA_ONE + att[k];
        k += 1;
    }
    r
}

/// The MLP hidden layer of layer `l` after ReLU, scale 2^32:
/// `m[i] = relu(sum over k of r[k] * win[k][i] + bin[i] * 2^8) >> 8`. Needs `l < 2`.
pub fn mlp_hidden(w: &Weights, l: usize, r: &[i64; D_MODEL]) -> [i64; D_MLP] {
    let mut m = [0i64; D_MLP];
    let mut i = 0;
    while i < D_MLP {
        let mut acc = 0i64;
        let mut k = 0;
        while k < D_MODEL {
            acc += r[k] * (w.layers[l].win[k][i] as i64);
            k += 1;
        }
        let pre = acc + w.layers[l].bin[i] * 256;
        if pre > 0 {
            m[i] = pre >> 8;
        }
        i += 1;
    }
    m
}

/// The MLP output of layer `l`, scale 2^40: `o[k] = sum over i of m[i] * wout[i][k] + bout[k]`.
/// Needs `l < 2`.
pub fn mlp_output(w: &Weights, l: usize, m: &[i64; D_MLP]) -> [i64; D_MODEL] {
    let mut o = [0i64; D_MODEL];
    let mut k = 0;
    while k < D_MODEL {
        let mut acc = 0i64;
        let mut i = 0;
        while i < D_MLP {
            acc += m[i] * (w.layers[l].wout[i][k] as i64);
            i += 1;
        }
        o[k] = acc + w.layers[l].bout[k];
        k += 1;
    }
    o
}

/// The final residual stream, scale 2^24: `(r * 2^8 + o) >> 16`.
pub fn final_stream(r: &[i64; D_MODEL], o: &[i64; D_MODEL]) -> [i64; D_MODEL] {
    let mut fin = [0i64; D_MODEL];
    let mut k = 0;
    while k < D_MODEL {
        fin[k] = (r[k] * 256 + o[k]) >> 16;
        k += 1;
    }
    fin
}

/// One causal layer pass over all active positions. `out[p]` is the scale-2^24 final stream of
/// layer `l` at position `p` for `p < seq_len`, and zero after. Needs `l < 2`,
/// `seq_len <= 32`.
pub fn layer_forward(w: &Weights, l: usize, x: &[[i64; D_MODEL]; MAX_SEQ], seq_len: usize) -> [[i64; D_MODEL]; MAX_SEQ] {
    let mut out = [[0i64; D_MODEL]; MAX_SEQ];
    let mut p = 0;
    while p < seq_len {
        let att = attention_at(w, l, x, p);
        let xp = row_at(x, p);
        let r = residual(&xp, &att);
        let m = mlp_hidden(w, l, &r);
        let o = mlp_output(w, l, &m);
        let f_p = final_stream(&r, &o);
        out[p] = f_p;
        p += 1;
    }
    out
}

/// Inter-layer rescale: `s = f[k] >> 16` clamped to `[-127, 127]`, restoring the
/// scale-2^8 embedding envelope for the next layer.
pub fn rescale_clamp(f: &[[i64; D_MODEL]; MAX_SEQ]) -> [[i64; D_MODEL]; MAX_SEQ] {
    let mut out = [[0i64; D_MODEL]; MAX_SEQ];
    let mut p = 0;
    while p < MAX_SEQ {
        let mut row = [0i64; D_MODEL];
        let mut k = 0;
        while k < D_MODEL {
            let s = f[p][k] >> 15;
            if s < -127 {
                row[k] = -127;
            } else if s > 127 {
                row[k] = 127;
            } else {
                row[k] = s;
            }
            k += 1;
        }
        out[p] = row;
        p += 1;
    }
    out
}

/// The logits over the full 256-token vocabulary, scale 2^32:
/// `out[v] = sum over k of fin[k] * (u[k][v] as i64)`.
pub fn unembed(w: &Weights, fin: &[i64; D_MODEL]) -> [i64; VOCAB] {
    let mut out = [0i64; VOCAB];
    let mut v = 0;
    while v < VOCAB {
        let mut acc = 0i64;
        let mut k = 0;
        while k < D_MODEL {
            acc += fin[k] * (w.u[k][v] as i64);
            k += 1;
        }
        out[v] = acc;
        v += 1;
    }
    out
}

/// Index of the largest entry of `l[0..vocab_size]`, the first one on a tie. Needs
/// `1 <= vocab_size <= 256`.
pub fn argmax(l: &[i64; VOCAB], vocab_size: usize) -> usize {
    let mut best = 0;
    let mut best_value = l[0];
    let mut c = 1;
    while c < vocab_size {
        if l[c] > best_value {
            best_value = l[c];
            best = c;
        }
        c += 1;
    }
    best
}

/// The logits of the full causal forward pass, `Some` when every guard passes:
/// `1 <= seq_len <= 32`, `1 <= w.n_layers <= 2`, `1 <= w.vocab_size <= 256`, and
/// `tokens[p] < 256` for all `p < seq_len`. The layer stack runs causally; between active
/// layers the stream is rescaled to scale 2^8 and clamped to `[-127, 127]`; after the last
/// active layer, the final stream of position `seq_len - 1` is unembedded. Never panics on
/// weights accepted by `load_check`.
pub fn forward_logits(w: &Weights, tokens: &[usize; MAX_SEQ], seq_len: usize) -> Option<[i64; VOCAB]> {
    if seq_len == 0 || seq_len > MAX_SEQ {
        return None;
    }
    if w.n_layers == 0 || w.n_layers > MAX_LAYERS {
        return None;
    }
    if w.vocab_size == 0 || w.vocab_size > VOCAB {
        return None;
    }
    let mut tokens_ok = true;
    let mut p = 0;
    while p < seq_len {
        if tokens[p] >= VOCAB {
            tokens_ok = false;
        }
        p += 1;
    }
    if !tokens_ok {
        return None;
    }
    let mut x = embed_all(w, tokens, seq_len);
    let mut last_hidden = [0i64; D_MODEL];
    let mut l = 0;
    while l < w.n_layers {
        let f = layer_forward(w, l, &x, seq_len);
        if l + 1 < w.n_layers {
            x = rescale_clamp(&f);
        } else {
            last_hidden = row_at(&f, seq_len - 1);
        }
        l += 1;
    }
    Some(unembed(w, &last_hidden))
}

/// `Some(argmax(logits))` for inputs accepted by `forward_logits`; `None` otherwise.
pub fn predict_next(w: &Weights, tokens: &[usize; MAX_SEQ], seq_len: usize) -> Option<usize> {
    let lg = forward_logits(w, tokens, seq_len);
    match lg {
        Some(l) => Some(argmax(&l, w.vocab_size)),
        None => None,
    }
}

/// Greedy causal generation: appends up to `steps` predicted tokens to `buf` from
/// `prompt_len` while the buffer is shorter than `MAX_SEQ`, and returns the final length.
/// `None` if any prediction is rejected. Never panics on weights accepted by `load_check`.
pub fn generate_greedy(w: &Weights, buf: &mut [usize; MAX_SEQ], prompt_len: usize, steps: usize) -> Option<usize> {
    let mut cur_len = prompt_len;
    let mut remaining = steps;
    let mut failed = false;
    while remaining > 0 && cur_len < MAX_SEQ && !failed {
        let toks = *buf;
        let next = predict_next(w, &toks, cur_len);
        match next {
            Some(t) => {
                buf[cur_len] = t;
                cur_len += 1;
                remaining -= 1;
            }
            None => {
                failed = true;
            }
        }
    }
    if failed {
        None
    } else {
        Some(cur_len)
    }
}
