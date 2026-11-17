//! Tests of the network on every input pair. These are tests, not the proof.

use mlp::fast::predict_fast;
use mlp::{P, predict};

#[test]
fn adds_mod_113_on_all_12769_pairs() {
    let mut pairs = 0;
    for a in 0..P {
        for b in 0..P {
            assert_eq!(predict(a, b), Some((a + b) % P), "predict({a}, {b})");
            pairs += 1;
        }
    }
    assert_eq!(pairs, 12_769);
}

#[test]
fn fast_agrees_with_safe_on_all_pairs_and_outside() {
    for a in 0..P + 3 {
        for b in 0..P + 3 {
            assert_eq!(predict_fast(a, b), predict(a, b), "({a}, {b})");
        }
    }
}

#[test]
fn out_of_range_is_none() {
    for &(a, b) in &[(P, 0), (0, P), (P, P), (usize::MAX, 0), (0, usize::MAX), (usize::MAX, usize::MAX)] {
        assert_eq!(predict(a, b), None);
        assert_eq!(predict_fast(a, b), None);
    }
}

/// A handful of pairs, small enough to run under Miri: `cargo +nightly miri test --test all_pairs few_pairs`.
#[test]
fn few_pairs() {
    for &(a, b) in &[(0, 0), (1, 112), (112, 112), (56, 57), (113, 0), (0, 113)] {
        assert_eq!(predict_fast(a, b), predict(a, b), "({a}, {b})");
    }
}
