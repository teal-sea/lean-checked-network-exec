use engine::*;
use transformer::weights as trained;
fn trained_weights() -> Weights {
    Weights {
        tok: trained::TOK,
        pos: trained::POS,
        wq: trained::WQ,
        wk: trained::WK,
        wv: trained::WV,
        wo: trained::WO,
        win: trained::WIN,
        bin: trained::BIN,
        wout: trained::WOUT,
        bout: trained::BOUT,
        u: trained::U,
        exp_n: trained::EXP_N,
        exp_2: trained::EXP_2,
        exp_1: trained::EXP_1,
        exp_0: trained::EXP_0,
    }
}
#[test]
fn exhaustive_logits() {
    let w = trained_weights();
    assert!(load_check(&w));
    let mut pairs = 0;
    for a in 0..113 {
        for b in 0..113 {
            assert_eq!(logits(&w, a, b), transformer::logits(a, b));
            // All logits equal also fixes tie-breaking. Compare the actual entry point too.
            assert_eq!(predict(&w, a, b), transformer::predict(a, b));
            pairs += 1;
        }
    }
    assert_eq!(pairs, 12769);
    assert_eq!(predict(&w, 113, 0), None);
    assert_eq!(predict(&w, 0, usize::MAX), None);
    println!("pairs={pairs}; logits={}; prediction_mismatches=0; logit_mismatches=0", pairs * 113);
}
#[test]
fn extreme_loaded_weights_do_not_overflow() {
    let w = Weights {
        tok: [[68; 128]; 114], pos: [[59; 128]; 3],
        wq: [[[5; 32]; 128]; 4], wk: [[[22; 32]; 128]; 4],
        wv: [[[106; 32]; 128]; 4], wo: [[[93; 128]; 32]; 4],
        win: [[82; 512]; 128], bin: [1 << 30; 512],
        wout: [[74; 128]; 512], bout: [1 << 37; 128], u: [[37; 113]; 128],
        exp_n: [EXP_ONE; 32], exp_2: [EXP_ONE; 256],
        exp_1: [EXP_ONE; 256], exp_0: [EXP_ONE; 256],
    };
    assert!(load_check(&w));
    assert_eq!(predict(&w, 0, 112), Some(0));
    assert!(logits(&w, 0, 112).unwrap().iter().all(|x| *x >= 0));
}

#[test]
fn rejects_bad_loads_and_accepts_other_weights() {
    let mut w = trained_weights();
    w.tok[0][0] = 69;
    assert!(!load_check(&w));
    w.tok[0][0] = 0;
    w.exp_n[0] = -1;
    assert!(!load_check(&w));
    w.exp_n[0] = EXP_ONE + 1;
    assert!(!load_check(&w));
    w.exp_n[0] = 0;
    w.bin[0] = i64::MIN;
    assert!(!load_check(&w));
    w.bin[0] = 0;
    assert!(load_check(&w));
    assert!(predict(&w, 0, 0).is_some());
}
