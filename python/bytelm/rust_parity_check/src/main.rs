//! Standalone parity check of the SPEC-E4-E6.md general engine: a GLMW v1
//! loader plus the exact integer forward, compared logit for logit against
//! `python/bytelm/ref_engine.py`.
//!
//! This is a test harness, not the verified crate: plain std Rust, nested
//! vectors, allocation allowed. The arithmetic is the contract's: every value
//! is an `i64`, `>>` is the arithmetic (floor) shift, the one division has a
//! nonnegative numerator and positive denominator so truncation and floor
//! agree, and `overflow-checks = true` in every profile makes any overflow a
//! panic instead of a silent wrap.
//!
//! Unlike the Python reference (which skips the output-dead positions of the
//! final layer), this binary computes EVERY active position at every layer,
//! literally as the spec's layer loop reads. The parity check therefore also
//! proves that the Python skip changes no output.
//!
//! Modes (first argument):
//!   logits BIN      read hex byte prompts from stdin, one per line; print one
//!                   line per prompt: seq_len then vocab_size logits
//!   mod113 BIN      run all 12,769 (a, b) pairs on [a, b, 113]; print wrong
//!                   count, accuracy and the FNV-1a 64 of all logits
//!   bench BIN N     greedy-generate from N pseudo-random 16-byte prompts;
//!                   print generated tokens, seconds and tokens/sec
//!   gen BIN HEX [STEPS]  greedy completion of one hex prompt, printed as hex

use std::env;
use std::fs;
use std::io::{self, BufRead, Write};
use std::time::Instant;

const MAX_LAYERS: usize = 2;
const VOCAB: usize = 256;
const MAX_SEQ: usize = 32;
const D_MODEL: usize = 128;
const N_HEADS: usize = 4;
const D_HEAD: usize = 32;
const D_MLP: usize = 512;
const EXP_ONE: i64 = 1 << 30;
const EXP_FRAC_BITS: u32 = 30;
const EXP_N_LEN: i64 = 32;
const ALPHA_ONE: i64 = 1 << 24;
const FILE_SIZE: usize = 479_504;

struct LayerW {
    wq: Vec<Vec<Vec<i64>>>, // [h][k][i]
    wk: Vec<Vec<Vec<i64>>>,
    wv: Vec<Vec<Vec<i64>>>,
    wo: Vec<Vec<Vec<i64>>>, // [h][t][k]
    win: Vec<Vec<i64>>,     // [k][i]
    bin: Vec<i64>,          // [i]
    wout: Vec<Vec<i64>>,    // [i][k]
    bout: Vec<i64>,         // [k]
}

struct Weights {
    n_layers: usize,
    vocab: usize,
    tok: Vec<Vec<i64>>, // [t][k]
    pos: Vec<Vec<i64>>, // [p][k]
    layers: Vec<LayerW>,
    u: Vec<Vec<i64>>, // [k][v]
    exp_n: Vec<i64>,
    exp_2: Vec<i64>,
    exp_1: Vec<i64>,
    exp_0: Vec<i64>,
}

// ---------------------------------------------------------------- GLMW loader

struct Cursor<'a> {
    data: &'a [u8],
    off: usize,
}

impl<'a> Cursor<'a> {
    fn i8s(&mut self, n: usize) -> Vec<i64> {
        let v: Vec<i64> = self.data[self.off..self.off + n].iter().map(|b| *b as i8 as i64).collect();
        self.off += n;
        v
    }
    fn i64s(&mut self, n: usize) -> Vec<i64> {
        let mut v = Vec::with_capacity(n);
        for _ in 0..n {
            let b: [u8; 8] = self.data[self.off..self.off + 8].try_into().unwrap();
            v.push(i64::from_le_bytes(b));
            self.off += 8;
        }
        v
    }
}

fn nest(flat: Vec<i64>, rows: usize, cols: usize) -> Vec<Vec<i64>> {
    assert_eq!(flat.len(), rows * cols);
    flat.chunks(cols).map(|c| c.to_vec()).collect()
}

fn nest3(flat: Vec<i64>, a: usize, b: usize, c: usize) -> Vec<Vec<Vec<i64>>> {
    assert_eq!(flat.len(), a * b * c);
    let mut out = Vec::with_capacity(a);
    for i in 0..a {
        let rows: Vec<Vec<i64>> = flat[i * b * c..(i + 1) * b * c]
            .chunks(c)
            .map(|ch| ch.to_vec())
            .collect();
        out.push(rows);
    }
    out
}

fn load(path: &str) -> Weights {
    let data = fs::read(path).expect("cannot read the weight file");
    assert_eq!(data.len(), FILE_SIZE, "GLMW v1 files are exactly 479,504 bytes");
    assert_eq!(&data[0..4], b"GLMW", "bad magic");
    let version = u32::from_le_bytes(data[4..8].try_into().unwrap());
    assert_eq!(version, 1, "bad version");
    let n_layers = u32::from_le_bytes(data[8..12].try_into().unwrap()) as usize;
    let vocab = u32::from_le_bytes(data[12..16].try_into().unwrap()) as usize;

    let mut cur = Cursor { data: &data, off: 16 };
    let tok = nest(cur.i8s(VOCAB * D_MODEL), 256, 128);
    let pos = nest(cur.i8s(MAX_SEQ * D_MODEL), 32, 128);
    let mut layers = Vec::with_capacity(MAX_LAYERS);
    for _ in 0..MAX_LAYERS {
        let wq = nest3(cur.i8s(N_HEADS * D_MODEL * D_HEAD), 4, 128, 32);
        let wk = nest3(cur.i8s(N_HEADS * D_MODEL * D_HEAD), 4, 128, 32);
        let wv = nest3(cur.i8s(N_HEADS * D_MODEL * D_HEAD), 4, 128, 32);
        let wo = nest3(cur.i8s(N_HEADS * D_HEAD * D_MODEL), 4, 32, 128);
        let win = nest(cur.i8s(D_MODEL * D_MLP), 128, 512);
        let bin = cur.i64s(D_MLP);
        let wout = nest(cur.i8s(D_MLP * D_MODEL), 512, 128);
        let bout = cur.i64s(D_MODEL);
        layers.push(LayerW { wq, wk, wv, wo, win, bin, wout, bout });
    }
    let u = nest(cur.i8s(D_MODEL * VOCAB), 128, 256);
    let exp_n = cur.i64s(32);
    let exp_2 = cur.i64s(256);
    let exp_1 = cur.i64s(256);
    let exp_0 = cur.i64s(256);
    assert_eq!(cur.off, FILE_SIZE, "trailing bytes");
    Weights { n_layers, vocab, tok, pos, layers, u, exp_n, exp_2, exp_1, exp_0 }
}

// ---------------------------------------------------------------- engine

fn exp_fix(w: &Weights, d: i64) -> i64 {
    if d <= 0 {
        return EXP_ONE;
    }
    let u = d >> 8;
    let n = u >> 24;
    if n >= EXP_N_LEN {
        return 0;
    }
    let mut e = w.exp_n[n as usize];
    e = (e * w.exp_2[((u >> 16) & 255) as usize]) >> EXP_FRAC_BITS;
    e = (e * w.exp_1[((u >> 8) & 255) as usize]) >> EXP_FRAC_BITS;
    e = (e * w.exp_0[(u & 255) as usize]) >> EXP_FRAC_BITS;
    e
}

fn forward_logits(w: &Weights, tokens: &[usize; MAX_SEQ], seq_len: usize) -> Option<Vec<i64>> {
    if seq_len == 0 || seq_len > MAX_SEQ {
        return None;
    }
    if w.n_layers == 0 || w.n_layers > MAX_LAYERS || w.vocab == 0 || w.vocab > VOCAB {
        return None;
    }
    for p in 0..seq_len {
        if tokens[p] >= VOCAB {
            return None;
        }
    }

    let mut x = vec![vec![0i64; D_MODEL]; MAX_SEQ];
    for p in 0..seq_len {
        for k in 0..D_MODEL {
            x[p][k] = w.tok[tokens[p]][k] + w.pos[p][k];
        }
    }

    let mut last_hidden = vec![0i64; D_MODEL];
    for l in 0..w.n_layers {
        let lw = &w.layers[l];
        let final_layer = l + 1 == w.n_layers;
        let mut nxt = vec![vec![0i64; D_MODEL]; MAX_SEQ];
        for p in 0..seq_len {
            // ---- causal attention over j <= p, four heads
            let mut att = vec![0i64; D_MODEL];
            for h in 0..N_HEADS {
                let mut q = vec![0i64; D_HEAD];
                for i in 0..D_HEAD {
                    let mut acc = 0i64;
                    for k in 0..D_MODEL {
                        acc += x[p][k] * lw.wq[h][k][i];
                    }
                    q[i] = acc;
                }
                let mut scores = vec![0i64; p + 1];
                for j in 0..=p {
                    let mut key = vec![0i64; D_HEAD];
                    for i in 0..D_HEAD {
                        let mut acc = 0i64;
                        for k in 0..D_MODEL {
                            acc += x[j][k] * lw.wk[h][k][i];
                        }
                        key[i] = acc;
                    }
                    let mut acc = 0i64;
                    for i in 0..D_HEAD {
                        acc += q[i] * key[i];
                    }
                    scores[j] = acc;
                }
                let mut smax = scores[0];
                for j in 1..=p {
                    if scores[j] > smax {
                        smax = scores[j];
                    }
                }
                let mut e = vec![0i64; p + 1];
                let mut den = 0i64;
                for j in 0..=p {
                    e[j] = exp_fix(w, smax - scores[j]);
                    den += e[j];
                }
                let mut alpha = vec![0i64; p + 1];
                for j in 0..=p {
                    // numerator >= 0, denominator > 0: `/` truncation == floor
                    alpha[j] = (e[j] * ALPHA_ONE) / den;
                }
                let mut vs: Vec<Vec<i64>> = Vec::with_capacity(p + 1);
                for j in 0..=p {
                    let mut v = vec![0i64; D_HEAD];
                    for i in 0..D_HEAD {
                        let mut acc = 0i64;
                        for k in 0..D_MODEL {
                            acc += x[j][k] * lw.wv[h][k][i];
                        }
                        v[i] = acc;
                    }
                    vs.push(v);
                }
                let mut z = vec![0i64; D_HEAD];
                for i in 0..D_HEAD {
                    let mut acc = 0i64;
                    for j in 0..=p {
                        acc += alpha[j] * vs[j][i];
                    }
                    z[i] = acc >> 16;
                }
                for k in 0..D_MODEL {
                    let mut acc = 0i64;
                    for t in 0..D_HEAD {
                        acc += z[t] * lw.wo[h][t][k];
                    }
                    att[k] += acc;
                }
            }

            // ---- residual, MLP, final stream
            let mut r = vec![0i64; D_MODEL];
            for k in 0..D_MODEL {
                r[k] = x[p][k] * ALPHA_ONE + att[k];
            }
            let mut m = vec![0i64; D_MLP];
            for i in 0..D_MLP {
                let mut acc = 0i64;
                for k in 0..D_MODEL {
                    acc += r[k] * lw.win[k][i];
                }
                let pre = acc + lw.bin[i] * 256;
                if pre > 0 {
                    m[i] = pre >> 8;
                }
            }
            let mut f = vec![0i64; D_MODEL];
            for k in 0..D_MODEL {
                let mut acc = 0i64;
                for i in 0..D_MLP {
                    acc += m[i] * lw.wout[i][k];
                }
                let o = acc + lw.bout[k];
                f[k] = (r[k] * 256 + o) >> 16;
            }

            if final_layer {
                if p + 1 == seq_len {
                    last_hidden = f;
                }
            } else {
                for k in 0..D_MODEL {
                    let s = f[k] >> 16;
                    nxt[p][k] = if s < -127 { -127 } else if s > 127 { 127 } else { s };
                }
            }
        }
        if !final_layer {
            x = nxt;
        }
    }

    let mut logits = vec![0i64; w.vocab];
    for v in 0..w.vocab {
        let mut acc = 0i64;
        for k in 0..D_MODEL {
            acc += last_hidden[k] * w.u[k][v];
        }
        logits[v] = acc;
    }
    Some(logits)
}

fn argmax_first(logits: &[i64]) -> usize {
    let mut best = 0usize;
    let mut best_value = logits[0];
    for c in 1..logits.len() {
        if logits[c] > best_value {
            best_value = logits[c];
            best = c;
        }
    }
    best
}

fn predict_next(w: &Weights, tokens: &[usize; MAX_SEQ], seq_len: usize) -> Option<usize> {
    let logits = forward_logits(w, tokens, seq_len)?;
    Some(argmax_first(&logits))
}

fn generate_greedy(w: &Weights, prompt: &[usize], steps: usize) -> Option<Vec<usize>> {
    let start = prompt.len().saturating_sub(MAX_SEQ);
    let mut buf: Vec<usize> = prompt[start..].to_vec();
    let mut cur = buf.len();
    if cur == 0 {
        return None;
    }
    let mut tokens = [0usize; MAX_SEQ];
    let mut generated = 0usize;
    while generated < steps {
        if cur >= MAX_SEQ {
            break;
        }
        for i in 0..cur {
            tokens[i] = buf[i];
        }
        let nxt = predict_next(w, &tokens, cur)?;
        buf.push(nxt);
        cur += 1;
        generated += 1;
    }
    Some(buf)
}

// ---------------------------------------------------------------- modes

fn fnv1a64(data: &[u8], mut state: u64) -> u64 {
    for b in data {
        state ^= *b as u64;
        state = state.wrapping_mul(0x100000001B3);
    }
    state
}

fn hex_to_bytes(s: &str) -> Vec<usize> {
    let s = s.trim();
    assert!(s.len() % 2 == 0, "hex prompt of odd length");
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap() as usize)
        .collect()
}

fn bytes_to_hex(b: &[usize]) -> String {
    let mut s = String::new();
    for v in b {
        s.push_str(&format!("{:02x}", v));
    }
    s
}

fn mode_logits(w: &Weights) {
    let stdin = io::stdin();
    let mut lock = stdin.lock();
    let mut line = String::new();
    let stdout = io::stdout();
    let mut out = io::BufWriter::new(stdout.lock());
    while lock.read_line(&mut line).unwrap() > 0 {
        let prompt = hex_to_bytes(&line);
        line.clear();
        if prompt.is_empty() {
            continue;
        }
        let mut tokens = [0usize; MAX_SEQ];
        let seq_len = prompt.len().min(MAX_SEQ);
        for i in 0..seq_len {
            tokens[i] = prompt[i];
        }
        let logits = forward_logits(w, &tokens, seq_len).expect("guard rejected a prompt");
        write!(out, "{}", seq_len).unwrap();
        for v in logits {
            write!(out, " {}", v).unwrap();
        }
        writeln!(out).unwrap();
    }
    out.flush().unwrap();
}

fn mode_mod113(w: &Weights) {
    assert_eq!(w.n_layers, 1);
    assert_eq!(w.vocab, 113);
    let p: usize = 113;
    let eq: usize = 113;
    let mut wrong = 0usize;
    let mut state: u64 = 0xCBF29CE484222325;
    for a in 0..p {
        for b in 0..p {
            let tokens = [a, b, eq, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0];
            let logits = forward_logits(w, &tokens, 3).unwrap();
            state = fnv1a64(
                &(0..p).flat_map(|c| logits[c].to_le_bytes()).collect::<Vec<u8>>(),
                state,
            );
            if argmax_first(&logits) != (a + b) % p {
                wrong += 1;
            }
        }
    }
    println!("pairs {}", p * p);
    println!("wrong {}", wrong);
    println!("accuracy {}/{}", p * p - wrong, p * p);
    println!("logits_fnv1a64 {:016x}", state);
}

fn mode_bench(w: &Weights, n: usize) {
    let mut lcg: u64 = 0x20261120;
    let mut prompts: Vec<Vec<usize>> = Vec::with_capacity(n);
    for _ in 0..n {
        let mut p = Vec::with_capacity(16);
        for _ in 0..16 {
            lcg = lcg.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            p.push((lcg >> 33) as usize & 255);
        }
        prompts.push(p);
    }
    let t0 = Instant::now();
    let mut tokens_out = 0usize;
    for prompt in &prompts {
        let buf = generate_greedy(w, prompt, MAX_SEQ).expect("guard rejected a bench prompt");
        tokens_out += buf.len() - prompt.len();
    }
    let secs = t0.elapsed().as_secs_f64();
    println!("prompts {}", n);
    println!("generated_tokens {}", tokens_out);
    println!("seconds {:.4}", secs);
    println!("tokens_per_second {:.1}", tokens_out as f64 / secs);
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: rust_parity_check <logits|mod113|bench|gen> BIN [N | HEX [STEPS]]");
        std::process::exit(2);
    }
    let mode = args[1].as_str();
    let w = load(&args[2]);
    match mode {
        "logits" => mode_logits(&w),
        "mod113" => mode_mod113(&w),
        "bench" => {
            let n: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(256);
            mode_bench(&w, n);
        }
        "gen" => {
            let prompt = hex_to_bytes(args.get(3).expect("gen needs a hex prompt"));
            let steps: usize = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(MAX_SEQ);
            let buf = generate_greedy(&w, &prompt, steps).expect("guard rejected the prompt");
            println!("{}", bytes_to_hex(&buf));
        }
        other => {
            eprintln!("unknown mode {other}");
            std::process::exit(2);
        }
    }
}
