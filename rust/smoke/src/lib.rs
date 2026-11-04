//! Step 0 smoke test: a loop over a slice, translated by Charon and Aeneas (scripts/translate.sh).
#![forbid(unsafe_code)]

/// Checked sum of a slice of `u32`: overflow panics (overflow checks are on in every profile).
pub fn sum(xs: &[u32]) -> u32 {
    let mut acc: u32 = 0;
    let mut i: usize = 0;
    while i < xs.len() {
        acc += xs[i];
        i += 1;
    }
    acc
}
