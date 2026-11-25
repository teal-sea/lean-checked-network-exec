use general_engine::{argmax, load_check, rescale_clamp, softmax_at, LayerWeights, Weights,
                     D_HEAD, D_MLP, D_MODEL, EXP_ONE, MAX_SEQ, N_HEADS, VOCAB};

fn layer() -> LayerWeights {
    LayerWeights {
        wq: [[[0; D_HEAD]; D_MODEL]; N_HEADS],
        wk: [[[0; D_HEAD]; D_MODEL]; N_HEADS],
        wv: [[[0; D_HEAD]; D_MODEL]; N_HEADS],
        wo: [[[0; D_MODEL]; D_HEAD]; N_HEADS],
        win: [[0; D_MLP]; D_MODEL],
        bin: [0; D_MLP],
        wout: [[0; D_MODEL]; D_MLP],
        bout: [0; D_MODEL],
    }
}

fn main() {
    let mut f = [[0; D_MODEL]; MAX_SEQ];
    f[0][..5].copy_from_slice(&[65536, 98304, -98304, 127 * 65536, -128 * 65536]);
    let shifted = rescale_clamp(&f);

    let w = Weights {
        n_layers: 1, vocab_size: 3, tok: [[0; D_MODEL]; VOCAB],
        pos: [[0; D_MODEL]; MAX_SEQ], layers: [layer(), layer()],
        u: [[0; VOCAB]; D_MODEL], exp_n: [EXP_ONE; 32],
        exp_2: [EXP_ONE; 256], exp_1: [EXP_ONE; 256], exp_0: [EXP_ONE; 256],
    };
    assert!(load_check(&w));
    // Equal scores make each exp EXP_ONE, giving den = 2 * EXP_ONE.
    let a = softmax_at(&w, &[10; MAX_SEQ], 1);

    // The higher sentinel is outside the runtime vocabulary.
    let mut logits = [0; VOCAB];
    logits[..4].copy_from_slice(&[3, 9, 9, 10]);
    let best = argmax(&logits, 3);
    println!("{{\"shift\":{:?},\"alpha\":{:?},\"tie\":{}}}",
             &shifted[0][..6], [a[0], a[1], a[0] + a[1], a[2]], best);
}
