//! The same network as `crate::predict`, written with raw pointers and no bounds checks.
//!
//! Every `unsafe` block states why its pointer reads stay inside the table rows.

use crate::{E1, E2, HID, P, W2};

/// The network's answer for the pair `(a, b)`, as `crate::predict` computes it.
pub fn predict_fast(a: usize, b: usize) -> Option<usize> {
    if a >= P || b >= P {
        return None;
    }
    let mut h: [i32; HID] = [0; HID];
    // SAFETY: a < P and b < P were checked above, so both rows exist.
    let row_a: *const i8 = unsafe { E1.get_unchecked(a) }.as_ptr();
    let row_b: *const i8 = unsafe { E2.get_unchecked(b) }.as_ptr();
    let hp: *mut i32 = h.as_mut_ptr();
    let mut k: usize = 0;
    while k < HID {
        // SAFETY: k < HID, and each row and `h` hold HID elements.
        unsafe {
            let s: i32 = *row_a.add(k) as i32 + *row_b.add(k) as i32;
            *hp.add(k) = s * s;
        }
        k += 1;
    }
    let hq: *const i32 = h.as_ptr();
    let mut best: usize = 0;
    // SAFETY: 0 < P.
    let mut best_score: i64 = unsafe { score_fast(hq, 0) };
    let mut c: usize = 1;
    while c < P {
        // SAFETY: c < P, and `hq` points to the HID initialized elements of `h`.
        let s: i64 = unsafe { score_fast(hq, c) };
        if s > best_score {
            best = c;
            best_score = s;
        }
        c += 1;
    }
    Some(best)
}

/// The score of candidate answer `c`.
///
/// # Safety
///
/// `h` must point to `HID` initialized `i32` values that stay valid for reads during the call,
/// and `c` must be below `P`.
unsafe fn score_fast(h: *const i32, c: usize) -> i64 {
    // SAFETY: c < P by the caller's contract.
    let row: *const i8 = unsafe { W2.get_unchecked(c) }.as_ptr();
    let mut acc: i64 = 0;
    let mut k: usize = 0;
    while k < HID {
        // SAFETY: k < HID; `row` has HID elements and `h` points to HID elements.
        acc += unsafe { (*row.add(k) as i64) * (*h.add(k) as i64) };
        k += 1;
    }
    acc
}
