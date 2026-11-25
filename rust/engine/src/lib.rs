//! Runtime-weights integer transformer. Call `load_check` once before evaluation.
//! Arithmetic, shifts and tie-breaking match `transformer`; weights are never compiled in.
#![no_std]
#![forbid(unsafe_code)]

pub const EXP_ONE: i64 = 1 << 30;
pub const EXP_FRAC_BITS: u32 = 30;

/// Fixed dimensions enforce every shape requirement at the Rust type boundary.
pub struct Weights {
    pub tok: [[i8; 128]; 114],
    pub pos: [[i8; 128]; 3],
    pub wq: [[[i8; 32]; 128]; 4],
    pub wk: [[[i8; 32]; 128]; 4],
    pub wv: [[[i8; 32]; 128]; 4],
    pub wo: [[[i8; 128]; 32]; 4],
    pub win: [[i8; 512]; 128],
    pub bin: [i64; 512],
    pub wout: [[i8; 128]; 512],
    pub bout: [i64; 128],
    pub u: [[i8; 113]; 128],
    pub exp_n: [i64; 32],
    pub exp_2: [i64; 256],
    pub exp_1: [i64; 256],
    pub exp_0: [i64; 256],
}

/// The numeric inner loop used by `head_scores`.
pub fn dot(x: &[i64; 32], y: &[i64; 32]) -> i64 {
    let mut acc = 0i64;
    let mut i = 0;
    while i < 32 {
        acc += x[i] * y[i];
        i += 1;
    }
    acc
}

fn bounded_i8<const N: usize>(xs: &[i8; N], limit: i8) -> bool {
    let mut i = 0;
    while i < N {
        if xs[i] < -limit || xs[i] > limit { return false; }
        i += 1;
    }
    true
}
fn bounded_i64<const N: usize>(xs: &[i64; N], limit: i64) -> bool {
    let mut i = 0;
    while i < N {
        if xs[i] < -limit || xs[i] > limit { return false; }
        i += 1;
    }
    true
}
fn table<const N: usize>(xs: &[i64; N]) -> bool {
    let mut i = 0;
    while i < N {
        if xs[i] < 0 || xs[i] > EXP_ONE { return false; }
        i += 1;
    }
    true
}

/// Sufficient, not necessary, magnitude bounds. The derivation is in SCOPE-engine.md.
/// All arrays have their required shapes by construction. Tables may be arbitrary in
/// [0, 2^30]: the maximal score uses exp_fix(0) = 2^30 independently of table entries.
pub fn load_check(w: &Weights) -> bool {
    let mut valid = true;
    let mut i = 0;
    while i < 114 { if !bounded_i8(&w.tok[i], 68) { valid = false; } i += 1; }
    i = 0;
    while i < 3 { if !bounded_i8(&w.pos[i], 59) { valid = false; } i += 1; }
    let mut h = 0;
    while h < 4 {
        i = 0;
        while i < 128 {
            if !bounded_i8(&w.wq[h][i], 5) || !bounded_i8(&w.wk[h][i], 22)
                || !bounded_i8(&w.wv[h][i], 106) { valid = false; }
            i += 1;
        }
        i = 0;
        while i < 32 { if !bounded_i8(&w.wo[h][i], 93) { valid = false; } i += 1; }
        h += 1;
    }
    i = 0;
    while i < 128 {
        if !bounded_i8(&w.win[i], 82) || !bounded_i8(&w.u[i], 37) { valid = false; }
        i += 1;
    }
    i = 0;
    while i < 512 { if !bounded_i8(&w.wout[i], 74) { valid = false; } i += 1; }
    valid && bounded_i64(&w.bin, 1 << 30) && bounded_i64(&w.bout, 1 << 37)
        && table(&w.exp_n) && table(&w.exp_2) && table(&w.exp_1) && table(&w.exp_0)
}

/// The modulus. Inputs and answers are `0..113`.
pub const P: usize = 113;
/// Number of tokens: `0..113` and `=`.
pub const VOCAB: usize = 114;
/// The token `=`.
pub const EQ: usize = 113;
/// Number of positions: `a`, `b`, `=`.
pub const N_POS: usize = 3;
/// Width of the residual stream.
pub const D_MODEL: usize = 128;
/// Number of attention heads.
pub const N_HEADS: usize = 4;
/// Width of one head.
pub const D_HEAD: usize = 32;
/// Width of the MLP hidden layer.
pub const D_MLP: usize = 512;

/// A softmax weight of 1, scale 2^24.
pub const ALPHA_ONE: i64 = 1 << 24;
/// Number of entries of `weights.exp_n`. `exp_fix` returns 0 from this many whole units on.
pub const EXP_N_LEN: i64 = 32;

/// Token plus position embedding, scale 2^8. Needs `tok < 114` and `pos < 3`.
pub fn embed(weights: &Weights, tok: usize, pos: usize) -> [i64; D_MODEL] {
    let mut x = [0i64; D_MODEL];
    let mut k = 0;
    while k < D_MODEL {
        x[k] = weights.tok[tok][k] as i64 + weights.pos[pos][k] as i64;
        k += 1;
    }
    x
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

/// The three attention scores of head `h`, read at the last position, scale 2^32:
/// `s[j] = (x[2] * weights.wq[h]) . (x[j] * weights.wk[h])`. Needs `h < 4`.
pub fn head_scores(weights: &Weights, h: usize, x: &[[i64; D_MODEL]; N_POS]) -> [i64; N_POS] {
    let q = project(&x[2], &weights.wq[h]);
    let mut s = [0i64; N_POS];
    let mut j = 0;
    while j < N_POS {
        let key = project(&x[j], &weights.wk[h]);
        s[j] = dot(&q, &key);
        j += 1;
    }
    s
}

/// Integer stand-in for `2^30 * exp(-d / 2^32)`, for `d >= 0`.
///
/// `d` is cut to 24 fractional bits, `u = d >> 8`, and split as
/// `u = n * 2^24 + b2 * 2^16 + b1 * 2^8 + b0`. The result is the product of the four table
/// entries `weights.exp_n[n]`, `weights.exp_2[b2]`, `weights.exp_1[b1]`, `weights.exp_0[b0]`, with a shift by 30 after each
/// multiplication. It is `2^30` at `d = 0` and `0` when `n >= 32`. A negative `d` does not occur
/// in this program and gives `2^30`.
pub fn exp_fix(weights: &Weights, d: i64) -> i64 {
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
    let mut e = weights.exp_n[n as usize];
    e = (e * weights.exp_2[b2 as usize]) >> EXP_FRAC_BITS;
    e = (e * weights.exp_1[b1 as usize]) >> EXP_FRAC_BITS;
    e = (e * weights.exp_0[b0 as usize]) >> EXP_FRAC_BITS;
    e
}

/// The softmax of three scores, scale 2^24:
/// `alpha[j] = e[j] * 2^24 / (e[0] + e[1] + e[2])` with `e[j] = exp_fix(weights, max(s) - s[j])`.
/// The largest score has `e = 2^30`, so the denominator is at least `2^30`.
pub fn softmax_weights(weights: &Weights, s: &[i64; N_POS]) -> [i64; N_POS] {
    let mut smax = s[0];
    let mut j = 1;
    while j < N_POS {
        if s[j] > smax {
            smax = s[j];
        }
        j += 1;
    }
    let mut e = [0i64; N_POS];
    let mut den = 0i64;
    j = 0;
    while j < N_POS {
        e[j] = exp_fix(weights, smax - s[j]);
        den += e[j];
        j += 1;
    }
    let mut alpha = [0i64; N_POS];
    j = 0;
    while j < N_POS {
        alpha[j] = (e[j] * ALPHA_ONE) / den;
        j += 1;
    }
    alpha
}

/// What head `h` adds to the residual stream, scale 2^32. The value vectors `x[j] * weights.wv[h]`
/// (scale 2^16) are mixed with the softmax weights (scale 2^24), shifted down to scale 2^24,
/// and multiplied by `weights.wo[h]`. Needs `h < 4`.
pub fn head_output(weights: &Weights,
    h: usize,
    x: &[[i64; D_MODEL]; N_POS],
    alpha: &[i64; N_POS],
) -> [i64; D_MODEL] {
    let v0 = project(&x[0], &weights.wv[h]);
    let v1 = project(&x[1], &weights.wv[h]);
    let v2 = project(&x[2], &weights.wv[h]);
    let mut z = [0i64; D_HEAD];
    let mut i = 0;
    while i < D_HEAD {
        z[i] = (alpha[0] * v0[i] + alpha[1] * v1[i] + alpha[2] * v2[i]) >> 16;
        i += 1;
    }
    let mut out = [0i64; D_MODEL];
    let mut k = 0;
    while k < D_MODEL {
        let mut acc = 0i64;
        let mut t = 0;
        while t < D_HEAD {
            acc += z[t] * (weights.wo[h][t][k] as i64);
            t += 1;
        }
        out[k] = acc;
        k += 1;
    }
    out
}

/// The sum of the four heads' outputs, scale 2^32.
pub fn attention(weights: &Weights, x: &[[i64; D_MODEL]; N_POS]) -> [i64; D_MODEL] {
    let mut att = [0i64; D_MODEL];
    let mut h = 0;
    while h < N_HEADS {
        let s = head_scores(weights, h, x);
        let alpha = softmax_weights(weights, &s);
        let w = head_output(weights, h, x, &alpha);
        let mut k = 0;
        while k < D_MODEL {
            att[k] += w[k];
            k += 1;
        }
        h += 1;
    }
    att
}

/// The residual stream after attention, scale 2^32: `x2 * 2^24 + att`.
pub fn residual(x2: &[i64; D_MODEL], att: &[i64; D_MODEL]) -> [i64; D_MODEL] {
    let mut r = [0i64; D_MODEL];
    let mut k = 0;
    while k < D_MODEL {
        r[k] = x2[k] * ALPHA_ONE + att[k];
        k += 1;
    }
    r
}

/// The MLP hidden layer after ReLU, scale 2^32:
/// `m[i] = relu(sum over k of r[k] * weights.win[k][i] + weights.bin[i] * 2^8) >> 8`.
pub fn mlp_hidden(weights: &Weights, r: &[i64; D_MODEL]) -> [i64; D_MLP] {
    let mut m = [0i64; D_MLP];
    let mut i = 0;
    while i < D_MLP {
        let mut acc = 0i64;
        let mut k = 0;
        while k < D_MODEL {
            acc += r[k] * (weights.win[k][i] as i64);
            k += 1;
        }
        let pre = acc + weights.bin[i] * 256;
        if pre > 0 {
            m[i] = pre >> 8;
        }
        i += 1;
    }
    m
}

/// The MLP output, scale 2^40: `o[k] = sum over i of m[i] * weights.wout[i][k] + weights.bout[k]`.
pub fn mlp_output(weights: &Weights, m: &[i64; D_MLP]) -> [i64; D_MODEL] {
    let mut o = [0i64; D_MODEL];
    let mut k = 0;
    while k < D_MODEL {
        let mut acc = 0i64;
        let mut i = 0;
        while i < D_MLP {
            acc += m[i] * (weights.wout[i][k] as i64);
            i += 1;
        }
        o[k] = acc + weights.bout[k];
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

/// The 113 logits, scale 2^32: `out[c] = sum over k of fin[k] * weights.u[k][c]`.
pub fn unembed(weights: &Weights, fin: &[i64; D_MODEL]) -> [i64; P] {
    let mut out = [0i64; P];
    let mut c = 0;
    while c < P {
        let mut acc = 0i64;
        let mut k = 0;
        while k < D_MODEL {
            acc += fin[k] * (weights.u[k][c] as i64);
            k += 1;
        }
        out[c] = acc;
        c += 1;
    }
    out
}

/// Index of the largest entry, the first one on a tie.
pub fn argmax(l: &[i64; P]) -> usize {
    let mut best = 0;
    let mut best_value = l[0];
    let mut c = 1;
    while c < P {
        if l[c] > best_value {
            best_value = l[c];
            best = c;
        }
        c += 1;
    }
    best
}

/// The logits for the tokens `[a, b, =]`, scale 2^32. Needs `a < 113` and `b < 113`.
pub fn forward(weights: &Weights, a: usize, b: usize) -> [i64; P] {
    let x = [embed(weights, a, 0), embed(weights, b, 1), embed(weights, EQ, 2)];
    let att = attention(weights, &x);
    let r = residual(&x[2], &att);
    let m = mlp_hidden(weights, &r);
    let o = mlp_output(weights, &m);
    let fin = final_stream(&r, &o);
    unembed(weights, &fin)
}

/// `Some(logits)` for `a, b < 113`; `None` otherwise. Never panics.
pub fn logits(weights: &Weights, a: usize, b: usize) -> Option<[i64; P]> {
    if a >= P || b >= P {
        return None;
    }
    Some(forward(weights, a, b))
}

/// `Some(answer)` for `a, b < 113`; `None` otherwise. Never panics.
pub fn predict(weights: &Weights, a: usize, b: usize) -> Option<usize> {
    if a >= P || b >= P {
        return None;
    }
    let l = forward(weights, a, b);
    Some(argmax(&l))
}
