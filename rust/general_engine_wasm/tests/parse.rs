//! `GLMW` v1 deserialization edge cases, against the real fixtures. The fixture
//! helper writes into a caller-owned buffer, so no frame ever holds more than
//! one 480 KB copy.
use std::fs;
use std::path::PathBuf;

use general_engine::{MAX_SEQ, load_check, predict_next};
use general_engine_wasm::{GLMW_FILE_LEN, ZERO_WEIGHTS, parse_glmw_into};

fn fixture_into(name: &str, out: &mut [u8; GLMW_FILE_LEN]) {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("weights")
        .join(name);
    let bytes = fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    assert_eq!(bytes.len(), GLMW_FILE_LEN);
    out.copy_from_slice(&bytes);
}

#[test]
fn mod113_fixture_loads_and_predicts() {
    let mut buf = [0u8; GLMW_FILE_LEN];
    fixture_into("mod113_v1.bin", &mut buf);
    let mut w = ZERO_WEIGHTS;
    assert!(parse_glmw_into(&buf, &mut w), "parses");
    assert!(load_check(&w), "mod113_v1.bin must pass load_check");
    // (21, 56): the pair with the smallest margin in the frozen reference.
    let mut tokens = [0usize; MAX_SEQ];
    tokens[2] = 113;
    for &(a, b, want) in &[
        (21usize, 56usize, 77usize),
        (112, 112, 111),
        (0, 0, 0),
        (112, 0, 112),
    ] {
        tokens[0] = a;
        tokens[1] = b;
        assert_eq!(predict_next(&w, &tokens, 3), Some(want), "({a}, {b})");
    }
}

#[test]
fn bytelm_fixture_loads() {
    let mut buf = [0u8; GLMW_FILE_LEN];
    fixture_into("tiny_bytelm_v1.bin", &mut buf);
    let mut w = ZERO_WEIGHTS;
    assert!(parse_glmw_into(&buf, &mut w), "parses");
    assert!(load_check(&w), "tiny_bytelm_v1.bin must pass load_check");
    assert_eq!(w.n_layers, 2);
    assert_eq!(w.vocab_size, 256);
}

#[test]
fn out_of_bounds_weight_byte_is_rejected() {
    // tok[0][0] sits at file offset 16, the first payload byte. 69 > 68.
    let mut buf = [0u8; GLMW_FILE_LEN];
    fixture_into("mod113_v1.bin", &mut buf);
    buf[16] = 69;
    let mut w = ZERO_WEIGHTS;
    assert!(parse_glmw_into(&buf, &mut w), "still parses");
    assert!(
        !load_check(&w),
        "corrupt tok[0][0] = 69 must fail load_check"
    );
}

#[test]
fn bad_headers_are_rejected() {
    let mut buf = [0u8; GLMW_FILE_LEN];
    fixture_into("mod113_v1.bin", &mut buf);
    let base = buf;
    let mut w = ZERO_WEIGHTS;
    // (byte offset, replacement value, case name). Header: magic 0..4,
    // version 4..8, n_layers 8..12, vocab_size 12..16.
    let cases: [(usize, u8, &str); 5] = [
        (0, b'X', "bad magic"),
        (5, 2, "bad version"),
        (8, 0, "n_layers = 0"),
        (8, 3, "n_layers = 3 > MAX_LAYERS"),
        (12, 0, "vocab_size = 0"),
    ];
    for (off, value, what) in cases {
        buf = base;
        buf[off] = value;
        assert!(!parse_glmw_into(&buf, &mut w), "{what}");
    }
    // vocab_size = 257: low byte 1 and high byte 1 of the u32 at offset 12.
    buf = base;
    buf[12] = 1;
    buf[13] = 1;
    assert!(!parse_glmw_into(&buf, &mut w), "vocab_size = 257 > 256");
    // The restored buffer parses again.
    buf = base;
    assert!(parse_glmw_into(&buf, &mut w));
}
