//! The trained recurrent adder of `RnnAdder.Network`, evaluated in safe Rust.
//!
//! The network reads one pair of bits `(a, b)` per step, least significant bit first, keeps a
//! hidden state of `H` bits, and emits one sum bit per step. After the last step a carry bit is
//! read off the state. Every weight is an integer and every activation is a threshold at zero:
//!
//! ```text
//! step  h (a, b) = [ Wh h + Wxa a + Wxb b + bh > 0 ]      entry by entry
//! out   h (a, b) = [ Wo (step h (a, b)) + Woa a + Wob b + bo > 0 ]
//! carry h        = [ Wc h + bc > 0 ]
//! ```
//!
//! The function names follow `lean/RnnAdder/Network.lean`. The weights in `weights.rs` are
//! generated from `lean/RnnAdder/Trained.lean` by `scripts/gen_adder_weights.py`.
#![no_std]
#![forbid(unsafe_code)]

mod weights;
pub use weights::*;

/// The hidden state: one `bool` per unit.
pub type State = [bool; H];

/// Sum of the weights at the positions where the state is `true`.
fn dot_b(w: &[i32; H], h: &State) -> i32 {
    let mut acc: i32 = 0;
    let mut i: usize = 0;
    while i < H {
        if h[i] {
            acc += w[i];
        }
        i += 1;
    }
    acc
}

/// The threshold activation.
fn thr(z: i32) -> bool {
    z > 0
}

/// One step of the state.
pub fn step(h: &State, a: bool, b: bool) -> State {
    let mut next: State = [false; H];
    let mut i: usize = 0;
    while i < H {
        let mut z: i32 = dot_b(&WH[i], h);
        if a {
            z += WXA[i];
        }
        if b {
            z += WXB[i];
        }
        z += BH[i];
        next[i] = thr(z);
        i += 1;
    }
    next
}

/// The sum bit emitted at a step.
pub fn out(h: &State, a: bool, b: bool) -> bool {
    let next: State = step(h, a, b);
    let mut z: i32 = dot_b(&WO, &next);
    if a {
        z += WOA;
    }
    if b {
        z += WOB;
    }
    z += BO;
    thr(z)
}

/// The carry read off a state.
pub fn carry(h: &State) -> bool {
    thr(dot_b(&WC, h) + BC)
}

/// Runs the network over `xs`, least significant bit pair first, starting from `H0`.
///
/// Writes one sum bit per input pair into `sum` and returns the final carry. Returns `None`,
/// leaving `sum` unchanged, when `sum.len() != xs.len()`.
pub fn add_bits(xs: &[(bool, bool)], sum: &mut [bool]) -> Option<bool> {
    if sum.len() != xs.len() {
        return None;
    }
    let mut h: State = H0;
    let mut i: usize = 0;
    while i < xs.len() {
        let (a, b) = xs[i];
        sum[i] = out(&h, a, b);
        h = step(&h, a, b);
        i += 1;
    }
    Some(carry(&h))
}

/// The network as a 64-bit adder: feeds it the 64 bit pairs of `a` and `b`, least significant
/// first, and packs the 64 sum bits. Returns the packed sum and the final carry.
pub fn add_u64(a: u64, b: u64) -> (u64, bool) {
    let mut h: State = H0;
    let mut s: u64 = 0;
    let mut i: u32 = 0;
    while i < 64 {
        let abit: bool = (a >> i) & 1 == 1;
        let bbit: bool = (b >> i) & 1 == 1;
        if out(&h, abit, bbit) {
            s |= 1u64 << i;
        }
        h = step(&h, abit, bbit);
        i += 1;
    }
    (s, carry(&h))
}
