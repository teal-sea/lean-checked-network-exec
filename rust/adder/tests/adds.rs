//! Tests of the adder evaluator against ordinary integer addition. These are tests, not the proof.

use adder::{H0, REACH, add_bits, add_u64, carry, out, step};

/// A small deterministic generator (SplitMix64), so the tests need no dependency.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// The ripple-carry adder of `RnnAdder.addBits` and `RnnAdder.carryOut`, with carry-in false.
fn ripple(xs: &[(bool, bool)]) -> (Vec<bool>, bool) {
    let mut c = false;
    let mut bits = Vec::with_capacity(xs.len());
    for &(a, b) in xs {
        bits.push(a ^ b ^ c);
        c = (a && b) || (a && c) || (b && c);
    }
    (bits, c)
}

#[test]
fn every_sequence_up_to_length_9() {
    // 4^n sequences of length n; n = 0..=9 is 349,525 sequences.
    for n in 0..=9usize {
        let mut xs = vec![(false, false); n];
        let mut sum = vec![false; n];
        for code in 0..(1u32 << (2 * n)) {
            for (i, x) in xs.iter_mut().enumerate() {
                *x = ((code >> (2 * i)) & 1 == 1, (code >> (2 * i + 1)) & 1 == 1);
            }
            let c = add_bits(&xs, &mut sum).unwrap();
            let (want, want_c) = ripple(&xs);
            assert_eq!((&sum, c), (&want, want_c), "length {n}, code {code}");
        }
    }
}

#[test]
fn random_long_sequences() {
    let mut rng = Rng(1);
    for &n in &[64usize, 128, 1000, 10_000, 100_000] {
        for _ in 0..20 {
            let xs: Vec<(bool, bool)> = (0..n)
                .map(|_| {
                    let r = rng.next();
                    (r & 1 == 1, r & 2 == 2)
                })
                .collect();
            let mut sum = vec![false; n];
            let c = add_bits(&xs, &mut sum).unwrap();
            let (want, want_c) = ripple(&xs);
            assert!(sum == want && c == want_c, "length {n}");
        }
    }
}

#[test]
fn length_mismatch_returns_none_and_leaves_sum_alone() {
    let xs = [(true, true); 5];
    let mut sum = [true, false, true, false];
    assert_eq!(add_bits(&xs, &mut sum), None);
    assert_eq!(sum, [true, false, true, false]);
    let mut long = [true; 6];
    assert_eq!(add_bits(&xs, &mut long), None);
    assert_eq!(long, [true; 6]);
}

#[test]
fn add_u64_is_overflowing_add() {
    let edges = [0u64, 1, 2, 3, u64::MAX, u64::MAX - 1, 1 << 63, (1 << 63) - 1, 0x5555_5555_5555_5555, 0xAAAA_AAAA_AAAA_AAAA];
    for &a in &edges {
        for &b in &edges {
            assert_eq!(add_u64(a, b), a.overflowing_add(b), "{a} + {b}");
        }
    }
    let mut rng = Rng(2);
    for _ in 0..1_000_000 {
        let (a, b) = (rng.next(), rng.next());
        assert_eq!(add_u64(a, b), a.overflowing_add(b), "{a} + {b}");
    }
}

#[test]
fn reach_is_closed_and_carry_is_the_full_adder_carry() {
    // The finite check of `RnnAdder.transOk`, run here on the Rust evaluator.
    assert!(REACH.contains(&H0));
    assert!(!carry(&H0));
    for h in &REACH {
        for &(a, b) in &[(false, false), (false, true), (true, false), (true, true)] {
            let n = step(h, a, b);
            let c = carry(h);
            assert!(REACH.contains(&n));
            assert_eq!(carry(&n), (a && b) || (a && c) || (b && c));
            assert_eq!(out(h, a, b), a ^ b ^ c);
        }
    }
}
