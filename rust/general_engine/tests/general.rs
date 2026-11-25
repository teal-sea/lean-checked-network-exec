//! Gate E4 general-engine behaviour: causal generation up to `MAX_SEQ = 32` with
//! `n_layers = 2`, `vocab_size = 256`, and `load_check` rejection of out-of-range weights.
use general_engine::*;
use transformer::weights as trained;

fn trained_layer() -> LayerWeights {
    LayerWeights {
        wq: trained::WQ,
        wk: trained::WK,
        wv: trained::WV,
        wo: trained::WO,
        win: trained::WIN,
        bin: trained::BIN,
        wout: trained::WOUT,
        bout: trained::BOUT,
    }
}

fn zero_layer() -> LayerWeights {
    LayerWeights {
        wq: [[[0i8; 32]; 128]; 4],
        wk: [[[0i8; 32]; 128]; 4],
        wv: [[[0i8; 32]; 128]; 4],
        wo: [[[0i8; 128]; 32]; 4],
        win: [[0i8; 512]; 128],
        bin: [0i64; 512],
        wout: [[0i8; 128]; 512],
        bout: [0i64; 128],
    }
}

/// Two layers over the full byte vocabulary: layer 0 trained (mod-113 tokens), layer 1 a
/// copy of it, everything else zero padding.
fn two_layer_full_vocab() -> Box<Weights> {
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
    Box::new(Weights {
        n_layers: 2,
        vocab_size: 256,
        tok,
        pos,
        layers: [trained_layer(), trained_layer()],
        u: [[0i8; 256]; 128],
        exp_n: trained::EXP_N,
        exp_2: trained::EXP_2,
        exp_1: trained::EXP_1,
        exp_0: trained::EXP_0,
    })
}

/// Two layers over the byte vocabulary with layer 1 zero: the inter-layer rescale and clamp
/// are exercised with a real layer 0.
fn two_layer_zero_second() -> Box<Weights> {
    let mut w = two_layer_full_vocab();
    w.layers[1] = zero_layer();
    w
}

/// Every entry of every weight at the exact `load_check` bound, all exponential tables at
/// `EXP_ONE`: the worst case the envelope analysis admits.
fn extreme_two_layer() -> Box<Weights> {
    Box::new(Weights {
        n_layers: 2,
        vocab_size: 256,
        tok: [[68i8; 128]; 256],
        pos: [[59i8; 128]; 32],
        layers: [
            LayerWeights {
                wq: [[[5i8; 32]; 128]; 4],
                wk: [[[22i8; 32]; 128]; 4],
                wv: [[[106i8; 32]; 128]; 4],
                wo: [[[93i8; 128]; 32]; 4],
                win: [[82i8; 512]; 128],
                bin: [1i64 << 30; 512],
                wout: [[74i8; 128]; 512],
                bout: [1i64 << 37; 128],
            },
            LayerWeights {
                wq: [[[5i8; 32]; 128]; 4],
                wk: [[[22i8; 32]; 128]; 4],
                wv: [[[106i8; 32]; 128]; 4],
                wo: [[[93i8; 128]; 32]; 4],
                win: [[82i8; 512]; 128],
                bin: [-(1i64 << 30); 512],
                wout: [[-74i8; 128]; 512],
                bout: [-(1i64 << 37); 128],
            },
        ],
        u: [[37i8; 256]; 128],
        exp_n: [EXP_ONE; 32],
        exp_2: [EXP_ONE; 256],
        exp_1: [EXP_ONE; 256],
        exp_0: [EXP_ONE; 256],
    })
}

/// Deterministic small-magnitude weights inside every `load_check` bound, varying per entry.
fn small_two_layer() -> Box<Weights> {
    // xorshift on a u64, scaled into each bound.
    let mut state: u64 = 0x2545F4914F6CDD1D;
    let mut next = move |m: i64| -> i64 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        (state % (2 * m as u64 + 1)) as i64 - m
    };
    let mut tok = [[0i8; 128]; 256];
    for t in 0..256 {
        for k in 0..128 {
            tok[t][k] = next(68) as i8;
        }
    }
    let mut pos = [[0i8; 128]; 32];
    for p in 0..32 {
        for k in 0..128 {
            pos[p][k] = next(59) as i8;
        }
    }
    let mut layers = [zero_layer(), zero_layer()];
    for l in 0..2 {
        for h in 0..4 {
            for i in 0..128 {
                for j in 0..32 {
                    layers[l].wq[h][i][j] = next(5) as i8;
                    layers[l].wk[h][i][j] = next(22) as i8;
                    layers[l].wv[h][i][j] = next(106) as i8;
                }
            }
            for t in 0..32 {
                for k in 0..128 {
                    layers[l].wo[h][t][k] = next(93) as i8;
                }
            }
        }
        for i in 0..128 {
            for m in 0..512 {
                layers[l].win[i][m] = next(82) as i8;
            }
        }
        for m in 0..512 {
            for k in 0..128 {
                layers[l].wout[m][k] = next(74) as i8;
            }
        }
        for m in 0..512 {
            layers[l].bin[m] = next(1 << 30);
        }
        for k in 0..128 {
            layers[l].bout[k] = next(1 << 37);
        }
    }
    let mut u = [[0i8; 256]; 128];
    for k in 0..128 {
        for v in 0..256 {
            u[k][v] = next(37) as i8;
        }
    }
    // A softmax table that is never flat: exp_0 decaying from EXP_ONE.
    let mut exp_0 = [0i64; 256];
    let mut e = EXP_ONE;
    for i in 0..256 {
        exp_0[i] = e;
        e -= EXP_ONE / 4096;
    }
    Box::new(Weights {
        n_layers: 2,
        vocab_size: 256,
        tok,
        pos,
        layers,
        u,
        exp_n: [EXP_ONE; 32],
        exp_2: [EXP_ONE; 256],
        exp_1: [EXP_ONE; 256],
        exp_0,
    })
}

fn run_greedy(w: &Weights, prompt: &[usize], steps: usize) -> Option<usize> {
    let mut buf = [0usize; MAX_SEQ];
    for (i, t) in prompt.iter().enumerate() {
        buf[i] = *t;
    }
    let final_len = generate_greedy(w, &mut buf, prompt.len(), steps)?;
    assert!(final_len <= MAX_SEQ);
    assert!(final_len >= prompt.len());
    for t in buf[..final_len].iter() {
        assert!(*t < 256);
    }
    // Every prefix length is a valid evaluation: no panic anywhere up to MAX_SEQ.
    for len in 1..=final_len {
        let lg = forward_logits(w, &buf, len).unwrap();
        assert_eq!(lg.len(), VOCAB);
        let r = predict_next(w, &buf, len).unwrap();
        assert!(r < 256);
    }
    Some(final_len)
}

#[test]
fn two_layer_generation_reaches_max_seq() {
    let w = two_layer_full_vocab();
    assert!(load_check(&w));
    // 3 + 40 > 32: the buffer fills exactly to MAX_SEQ and generation stops there.
    assert_eq!(run_greedy(&w, &[5, 7, 113], 40), Some(32));
    let w2 = two_layer_zero_second();
    assert!(load_check(&w2));
    assert_eq!(run_greedy(&w2, &[5, 7, 113], 40), Some(32));
    // A prompt already at MAX_SEQ generates nothing.
    let prompt: Vec<usize> = (0..32).map(|i| (i * 7) % 256).collect();
    assert_eq!(run_greedy(&w, &prompt, 40), Some(32));
    // Zero steps: unchanged.
    assert_eq!(run_greedy(&w, &[5, 7, 113], 0), Some(3));
}

#[test]
fn two_layer_extreme_and_small_weights_do_not_overflow() {
    let w = extreme_two_layer();
    assert!(load_check(&w));
    assert_eq!(run_greedy(&w, &[200, 100, 0, 255], 40), Some(32));
    let w2 = small_two_layer();
    assert!(load_check(&w2));
    assert_eq!(run_greedy(&w2, &[0, 1, 2, 3, 4, 5, 6, 7], 40), Some(32));
    // One-layer, full-vocabulary variant also generates.
    let mut w3 = two_layer_full_vocab();
    w3.n_layers = 1;
    assert!(load_check(&w3));
    assert_eq!(run_greedy(&w3, &[5, 7, 113], 40), Some(32));
}

#[test]
fn load_check_rejects_out_of_range_weights() {
    let mut w = two_layer_full_vocab();
    assert!(load_check(&w));

    w.n_layers = 0;
    assert!(!load_check(&w));
    w.n_layers = 3;
    assert!(!load_check(&w));
    w.n_layers = 2;

    w.vocab_size = 0;
    assert!(!load_check(&w));
    w.vocab_size = 257;
    assert!(!load_check(&w));
    w.vocab_size = 256;

    w.tok[0][0] = 69;
    assert!(!load_check(&w));
    w.tok[0][0] = -69;
    assert!(!load_check(&w));
    w.tok[0][0] = 0;
    // A padding token row (t >= vocab_size) is still checked.
    w.tok[200][0] = 69;
    assert!(!load_check(&w));
    w.tok[200][0] = 0;

    w.pos[31][0] = 60;
    assert!(!load_check(&w));
    w.pos[31][0] = 0;

    w.layers[0].wq[0][0][0] = 6;
    assert!(!load_check(&w));
    w.layers[0].wq[0][0][0] = 0;
    w.layers[1].wq[3][127][31] = 6; // padding layer is checked too
    assert!(!load_check(&w));
    w.layers[1].wq[3][127][31] = 0;
    w.layers[1].wk[0][0][0] = 23;
    assert!(!load_check(&w));
    w.layers[1].wk[0][0][0] = 0;
    w.layers[0].wv[1][5][9] = 107;
    assert!(!load_check(&w));
    w.layers[0].wv[1][5][9] = 0;
    w.layers[0].wo[2][10][50] = 94;
    assert!(!load_check(&w));
    w.layers[0].wo[2][10][50] = 0;
    w.layers[0].win[7][300] = 83;
    assert!(!load_check(&w));
    w.layers[0].win[7][300] = 0;
    w.layers[0].wout[100][64] = 75;
    assert!(!load_check(&w));
    w.layers[0].wout[100][64] = 0;

    w.layers[0].bin[0] = i64::MAX;
    assert!(!load_check(&w));
    w.layers[0].bin[0] = -(1i64 << 30) - 1;
    assert!(!load_check(&w));
    w.layers[0].bin[0] = 0;
    w.layers[1].bin[511] = (1i64 << 30) + 1;
    assert!(!load_check(&w));
    w.layers[1].bin[511] = 0;
    w.layers[0].bout[127] = i64::MIN;
    assert!(!load_check(&w));
    w.layers[0].bout[127] = 0;
    w.layers[1].bout[0] = (1i64 << 37) + 1;
    assert!(!load_check(&w));
    w.layers[1].bout[0] = 0;

    w.u[127][255] = 38;
    assert!(!load_check(&w));
    w.u[127][255] = 0;

    w.exp_n[0] = -1;
    assert!(!load_check(&w));
    w.exp_n[0] = EXP_ONE + 1;
    assert!(!load_check(&w));
    w.exp_n[0] = 0;
    w.exp_2[255] = EXP_ONE + 1;
    assert!(!load_check(&w));
    w.exp_2[255] = 0;
    w.exp_1[128] = -1;
    assert!(!load_check(&w));
    w.exp_1[128] = 0;
    w.exp_0[1] = EXP_ONE + 1;
    assert!(!load_check(&w));
    w.exp_0[1] = 0;

    assert!(load_check(&w));
}
