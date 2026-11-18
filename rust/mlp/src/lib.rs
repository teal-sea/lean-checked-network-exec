//! The trained two-layer network of `LeanCheckedNetwork.Network`, evaluated in Rust.
//!
//! For an input pair `(a, b)` it takes row `a` of `E1` and row `b` of `E2`, adds them entry by
//! entry, squares each entry (one entry per neuron), and gives every candidate answer `c` the
//! score `sum over neurons of W2[c] * hidden`. The answer is the `c` with the highest score, the
//! first one on a tie. This is `answer` in lean-checked-network's
//! `lean/LeanCheckedNetwork/Network.lean`, on the tables of `network/trained.npz`.
//!
//! `predict` is safe Rust. `fast::predict_fast` computes the same thing through raw pointers,
//! with no bounds checks.
#![no_std]
#![deny(unsafe_op_in_unsafe_fn)]

mod weights;
pub use weights::*;

pub mod fast;

/// The hidden layer: `(E1[a][k] + E2[b][k])^2` for each neuron `k`. Requires `a < P` and `b < P`.
fn hidden(a: usize, b: usize) -> [i32; HID] {
    let mut h: [i32; HID] = [0; HID];
    let mut k: usize = 0;
    while k < HID {
        let s: i32 = E1[a][k] as i32 + E2[b][k] as i32;
        h[k] = s * s;
        k += 1;
    }
    h
}

/// The score of candidate answer `c`: the dot product of row `c` of `W2` with the hidden layer.
/// Requires `c < P`.
fn score(h: &[i32; HID], c: usize) -> i64 {
    let mut acc: i64 = 0;
    let mut k: usize = 0;
    while k < HID {
        acc += (W2[c][k] as i64) * (h[k] as i64);
        k += 1;
    }
    acc
}

/// The network's answer for the pair `(a, b)`: `Some(c)` with `c` the first index of the largest
/// score, or `None` when `a >= P` or `b >= P`.
pub fn predict(a: usize, b: usize) -> Option<usize> {
    if a >= P || b >= P {
        return None;
    }
    let h: [i32; HID] = hidden(a, b);
    let mut best: usize = 0;
    let mut best_score: i64 = score(&h, 0);
    let mut c: usize = 1;
    while c < P {
        let s: i64 = score(&h, c);
        if s > best_score {
            best = c;
            best_score = s;
        }
        c += 1;
    }
    Some(best)
}
