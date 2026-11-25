//! Gate E4 mod-113 equivalence: `general_engine` with `n_layers = 1`, `vocab_size = 113`
//! agrees bit-for-bit with the proved 1-layer `rust/transformer` on every pair `(a, b)` in
//! `0..113 × 0..113` (12,769 pairs), both on all 113 logits and on the predicted token.
use general_engine::*;
use transformer::weights as trained;

/// The trained mod-113 weights of `rust/transformer`, embedded as a `general_engine`
/// `Weights` with `n_layers = 1` and `vocab_size = 113`: token rows `0..114` and position
/// rows `0..3` come from the trained model, the vocabulary covers 256 tokens, `u` covers the
/// first 113 columns, layer 0 is the trained layer, layer 1 is zero padding.
fn general_from_trained() -> Box<Weights> {
    let mut tok = [[0i8; 128]; 256];
    for t in 0..114 {
        for k in 0..128 {
            tok[t][k] = trained::TOK[t][k];
        }
    }
    let mut pos = [[0i8; 128]; 32];
    for p in 0..3 {
        for k in 0..128 {
            pos[p][k] = trained::POS[p][k];
        }
    }
    let layer0 = LayerWeights {
        wq: trained::WQ,
        wk: trained::WK,
        wv: trained::WV,
        wo: trained::WO,
        win: trained::WIN,
        bin: trained::BIN,
        wout: trained::WOUT,
        bout: trained::BOUT,
    };
    let layer1 = LayerWeights {
        wq: [[[0i8; 32]; 128]; 4],
        wk: [[[0i8; 32]; 128]; 4],
        wv: [[[0i8; 32]; 128]; 4],
        wo: [[[0i8; 128]; 32]; 4],
        win: [[0i8; 512]; 128],
        bin: [0i64; 512],
        wout: [[0i8; 128]; 512],
        bout: [0i64; 128],
    };
    let mut u = [[0i8; 256]; 128];
    for k in 0..128 {
        for v in 0..113 {
            u[k][v] = trained::U[k][v];
        }
    }
    Box::new(Weights {
        n_layers: 1,
        vocab_size: 113,
        tok,
        pos,
        layers: [layer0, layer1],
        u,
        exp_n: trained::EXP_N,
        exp_2: trained::EXP_2,
        exp_1: trained::EXP_1,
        exp_0: trained::EXP_0,
    })
}

/// One worker's slice of the `(a, b)` grid: exact logit and prediction comparisons.
fn check_pairs(w: &Weights, a_lo: usize, a_hi: usize) -> (u64, u64, u64) {
    let mut pairs = 0u64;
    let mut logit_mismatches = 0u64;
    let mut prediction_mismatches = 0u64;
    for a in a_lo..a_hi {
        for b in 0..113 {
            let mut tokens = [0usize; MAX_SEQ];
            tokens[0] = a;
            tokens[1] = b;
            tokens[2] = 113;
            let lg = match forward_logits(w, &tokens, 3) {
                Some(l) => l,
                None => {
                    prediction_mismatches += 1;
                    continue;
                }
            };
            let expect = transformer::logits(a, b).unwrap();
            for v in 0..113 {
                if lg[v] != expect[v] {
                    logit_mismatches += 1;
                }
            }
            match predict_next(w, &tokens, 3) {
                Some(r) => {
                    if r != (a + b) % 113 {
                        prediction_mismatches += 1;
                    }
                    if r != transformer::predict(a, b).unwrap() {
                        prediction_mismatches += 1;
                    }
                }
                None => prediction_mismatches += 1,
            }
            pairs += 1;
        }
    }
    (pairs, logit_mismatches, prediction_mismatches)
}

#[test]
fn exhaustive_mod113() {
    let w = general_from_trained();
    assert!(load_check(&w));
    let threads = 8;
    let chunk = (113 + threads - 1) / threads;
    let mut pairs = 0u64;
    let mut logit_mismatches = 0u64;
    let mut prediction_mismatches = 0u64;
    std::thread::scope(|s| {
        let handles: Vec<_> = (0..threads)
            .map(|t| {
                let a_lo = t * chunk;
                let a_hi = ((t + 1) * chunk).min(113);
                let wt: &Weights = &w;
                s.spawn(move || check_pairs(wt, a_lo, a_hi))
            })
            .collect();
        for h in handles {
            let (p, l, m) = h.join().unwrap();
            pairs += p;
            logit_mismatches += l;
            prediction_mismatches += m;
        }
    });
    assert_eq!(pairs, 12769);
    assert_eq!(logit_mismatches, 0);
    assert_eq!(prediction_mismatches, 0);
    println!(
        "pairs={pairs}; logits={}; logit_mismatches=0; prediction_mismatches=0",
        pairs * 113
    );
}

#[test]
fn mod113_guards() {
    let w = general_from_trained();
    let mut tokens = [0usize; MAX_SEQ];
    tokens[0] = 5;
    tokens[1] = 7;
    tokens[2] = 113;
    assert_eq!(predict_next(&w, &tokens, 0), None);
    assert_eq!(predict_next(&w, &tokens, 33), None);
    tokens[1] = 256;
    assert_eq!(predict_next(&w, &tokens, 3), None);
    tokens[1] = usize::MAX;
    assert_eq!(predict_next(&w, &tokens, 3), None);
    tokens[1] = 7;
    assert_eq!(predict_next(&w, &tokens, 3), Some((5 + 7) % 113));
    // An out-of-range token at a position beyond seq_len must not be rejected.
    tokens[3] = 255;
    assert_eq!(predict_next(&w, &tokens, 3), Some((5 + 7) % 113));
    // Unloaded shapes.
    let mut bad = general_from_trained();
    bad.n_layers = 0;
    assert_eq!(forward_logits(&bad, &tokens, 3), None);
    bad.n_layers = 3;
    assert_eq!(forward_logits(&bad, &tokens, 3), None);
    bad.n_layers = 1;
    bad.vocab_size = 0;
    assert_eq!(forward_logits(&bad, &tokens, 3), None);
    bad.vocab_size = 257;
    assert_eq!(forward_logits(&bad, &tokens, 3), None);
    bad.vocab_size = 113;
    assert_eq!(predict_next(&bad, &tokens, 3), Some((5 + 7) % 113));
}
