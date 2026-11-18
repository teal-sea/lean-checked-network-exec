//! Exhaustive checks of the evaluator: all 12,769 pairs.
//!
//! `fixtures/python_reference.txt` is written by `scripts/check_transformer_int.py`, the Python
//! reference of the same program. The hash covers every logit of every pair, so a pass means the
//! Rust and the reference agree on all 1,442,897 logits.
#![forbid(unsafe_code)]

use transformer::{
    ALPHA_ONE, D_MODEL, EQ, N_HEADS, N_POS, P, argmax, embed, exp_fix, head_scores, logits,
    predict, softmax_weights, weights,
};

const REFERENCE: &str = include_str!("fixtures/python_reference.txt");

/// The value of `key` in the reference file.
fn reference(key: &str) -> &'static str {
    for line in REFERENCE.lines() {
        if let Some(rest) = line.strip_prefix(key) {
            if let Some(value) = rest.strip_prefix(' ') {
                return value.trim();
            }
        }
    }
    panic!("no `{key}` line in fixtures/python_reference.txt");
}

#[test]
fn every_pair_is_right_and_matches_the_reference() {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    let mut min_margin = i64::MAX;
    let mut min_pair = (0, 0);
    let mut pairs = 0;
    for a in 0..P {
        for b in 0..P {
            let want = (a + b) % P;
            let l = logits(a, b).expect("a and b are below 113");
            assert_eq!(argmax(&l), want, "argmax at ({a}, {b})");
            assert_eq!(predict(a, b), Some(want), "predict at ({a}, {b})");
            let mut runner_up = i64::MIN;
            for c in 0..P {
                if c != want && l[c] > runner_up {
                    runner_up = l[c];
                }
            }
            let margin = l[want] - runner_up;
            assert!(margin > 0, "margin {margin} at ({a}, {b})");
            if margin < min_margin {
                min_margin = margin;
                min_pair = (a, b);
            }
            for v in l {
                for byte in v.to_le_bytes() {
                    hash = (hash ^ u64::from(byte)).wrapping_mul(0x0000_0100_0000_01b3);
                }
            }
            pairs += 1;
        }
    }
    assert_eq!(pairs, 12_769);
    assert_eq!(format!("{hash:016x}"), reference("logits_fnv1a64"));
    assert_eq!(min_margin.to_string(), reference("min_margin"));
    assert_eq!(format!("{} {}", min_pair.0, min_pair.1), reference("min_margin_pair"));
}

#[test]
fn out_of_range_inputs_give_none() {
    let big = usize::MAX;
    let cases = [
        (P, 0),
        (0, P),
        (P, P),
        (P + 1, 5),
        (5, P + 1),
        (big, 0),
        (0, big),
        (big, big),
        (112, P),
        (P, 112),
    ];
    for (a, b) in cases {
        assert_eq!(predict(a, b), None, "predict at ({a}, {b})");
        assert!(logits(a, b).is_none(), "logits at ({a}, {b})");
    }
    assert_eq!(predict(112, 112), Some(111));
}

#[test]
fn exp_fix_endpoints_and_accuracy() {
    assert_eq!(exp_fix(0), weights::EXP_ONE);
    assert_eq!(exp_fix(-1), weights::EXP_ONE);
    assert_eq!(exp_fix(i64::MIN), weights::EXP_ONE);
    assert_eq!(exp_fix(32 << 32), 0);
    assert_eq!(exp_fix(i64::MAX), 0);
    // exp(-1) and exp(-2) at 30 fractional bits are the table entries themselves.
    assert_eq!(exp_fix(1 << 32), weights::EXP_N[1]);
    assert_eq!(exp_fix(2 << 32), weights::EXP_N[2]);
    // Within 72 units of 2^-30 of the real exponential, on 200,000 seeded inputs below 40 units.
    // Cutting `d` to 24 fractional bits accounts for up to 64 of them. The function is not
    // monotone: where the result is small, a step to the next table entry can add one unit.
    let mut state: u64 = 20_261_117;
    let mut samples = 0;
    while samples < 200_000 {
        state = state.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1_442_695_040_888_963_407);
        let d = ((state >> 20) % (40 << 32)) as i64;
        let e = exp_fix(d);
        let real = (weights::EXP_ONE as f64) * (-(d as f64) / 4_294_967_296.0).exp();
        let error = e as f64 - real;
        assert!(0 <= e && e <= weights::EXP_ONE, "exp_fix({d}) = {e}");
        assert!(error.abs() <= 72.0, "exp_fix({d}) = {e}, real {real}");
        samples += 1;
    }
}

#[test]
fn softmax_weights_sum_to_one_within_three_units() {
    for a in [0, 1, 56, 112] {
        for b in [0, 21, 73, 112] {
            let x = [embed(a, 0), embed(b, 1), embed(EQ, 2)];
            assert_eq!(x[2].len(), D_MODEL);
            for h in 0..N_HEADS {
                let alpha = softmax_weights(&head_scores(h, &x));
                let mut total = 0;
                for j in 0..N_POS {
                    assert!(alpha[j] >= 0);
                    total += alpha[j];
                }
                assert!(ALPHA_ONE - 3 < total && total <= ALPHA_ONE, "sum {total}");
            }
        }
    }
}
