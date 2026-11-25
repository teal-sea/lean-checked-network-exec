//! C-ABI WebAssembly wrapper around `general_engine` (gate E6).
//!
//! The browser writes a `GLMW` v1 weight file (exactly `GLMW_FILE_LEN` bytes) into
//! the buffer returned by `wasm_get_weight_buf_ptr`, then calls `wasm_load_weights`,
//! which deserializes it, runs `general_engine::load_check` and keeps the struct only
//! if every bound holds. All arithmetic is `general_engine`'s; the greedy path is
//! 100% the proved crate. The one sampling helper adds only a top-k choice and a
//! seeded uniform draw on top of the engine's own `exp_fix` tables.
//!
//! State is held in `RefCell` statics: the WebAssembly instance is single threaded
//! and the exports are not reentrant, so at most one borrow is live at a time.
//! The code never touches std; the crate is `no_std` exactly on the WebAssembly
//! target, so host builds can still run `cargo test` and the examples, and the
//! shipped `.wasm` contains no std.
#![cfg_attr(target_family = "wasm", no_std)]
#![deny(unsafe_code)]

use core::cell::{Ref, RefCell, RefMut};

use general_engine::{
    D_HEAD, D_MLP, D_MODEL, EXP_ONE, MAX_LAYERS, MAX_SEQ, N_HEADS, VOCAB, Weights,
};

/// A `RefCell` in a `static`. The WebAssembly instance is single-threaded and
/// none of the exported functions reenter or call each other, so at most one
/// borrow is ever live. The one `unsafe impl` below states exactly that.
pub(crate) struct SyncCell<T>(RefCell<T>);

impl<T> SyncCell<T> {
    pub const fn new(value: T) -> Self {
        SyncCell(RefCell::new(value))
    }

    pub fn borrow(&self) -> Ref<'_, T> {
        self.0.borrow()
    }

    pub fn borrow_mut(&self) -> RefMut<'_, T> {
        self.0.borrow_mut()
    }
}

// SAFETY: see the struct comment. Every borrow is released before an exported
// function returns, and the browser calls exports sequentially on one thread.
#[allow(unsafe_code)]
unsafe impl<T> Sync for SyncCell<T> {}

/// Length of a whole `GLMW` v1 file: 16-byte header plus the packed weights.
pub const GLMW_FILE_LEN: usize = 479_504;
/// Length of the weight payload after the header.
pub const GLMW_PAYLOAD_LEN: usize = GLMW_FILE_LEN - 16;
/// The file magic.
pub const GLMW_MAGIC: [u8; 4] = *b"GLMW";
/// The file version.
pub const GLMW_VERSION: u32 = 1;

static BUF: SyncCell<[u8; GLMW_FILE_LEN]> = SyncCell::new([0u8; GLMW_FILE_LEN]);
static WEIGHTS: SyncCell<Weights> = SyncCell::new(ZERO_WEIGHTS);
static LOADED: SyncCell<bool> = SyncCell::new(false);
static TOKENS: SyncCell<[u32; MAX_SEQ]> = SyncCell::new([0u32; MAX_SEQ]);
static LOGITS: SyncCell<[i64; VOCAB]> = SyncCell::new([0i64; VOCAB]);

/// The `no_std` panic handler for the WebAssembly build. A trap is better than a
/// hang if the no-panic proof is ever wrong. Host builds link std and use its
/// handler instead.
#[cfg(target_family = "wasm")]
#[panic_handler]
#[allow(unsafe_code)]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

fn read_u32(buf: &[u8], off: usize) -> u32 {
    (buf[off] as u32)
        | ((buf[off + 1] as u32) << 8)
        | ((buf[off + 2] as u32) << 16)
        | ((buf[off + 3] as u32) << 24)
}

fn read_i64(buf: &[u8], off: usize) -> i64 {
    let mut v = 0i64;
    let mut i = 0;
    while i < 8 {
        v |= (buf[off + i] as i64) << (8 * i);
        i += 1;
    }
    v
}

/// Deserializes the `GLMW` v1 file in `buf` into the caller's `Weights`, so no
/// ~480 KB struct ever sits in a stack frame. `Some(())` on success, `None` if
/// the header is wrong or a dimension field is out of range. Every entry of `out`
/// is overwritten, so no blank initialization is needed. Never panics, never
/// reads out of bounds.
pub fn parse_glmw_into(buf: &[u8; GLMW_FILE_LEN], out: &mut Weights) -> bool {
    if buf[0] != GLMW_MAGIC[0]
        || buf[1] != GLMW_MAGIC[1]
        || buf[2] != GLMW_MAGIC[2]
        || buf[3] != GLMW_MAGIC[3]
    {
        return false;
    }
    if read_u32(buf, 4) != GLMW_VERSION {
        return false;
    }
    let n_layers = read_u32(buf, 8) as usize;
    let vocab_size = read_u32(buf, 12) as usize;
    if n_layers < 1 || n_layers > MAX_LAYERS || vocab_size < 1 || vocab_size > VOCAB {
        return false;
    }
    out.n_layers = n_layers;
    out.vocab_size = vocab_size;
    let mut off = 16usize;
    let mut t = 0;
    while t < VOCAB {
        let mut k = 0;
        while k < D_MODEL {
            out.tok[t][k] = buf[off] as i8;
            off += 1;
            k += 1;
        }
        t += 1;
    }
    let mut p = 0;
    while p < MAX_SEQ {
        let mut k = 0;
        while k < D_MODEL {
            out.pos[p][k] = buf[off] as i8;
            off += 1;
            k += 1;
        }
        p += 1;
    }
    let mut l = 0;
    while l < MAX_LAYERS {
        let layer = &mut out.layers[l];
        // The file stores each attention matrix whole: all N_HEADS heads of wq,
        // then all of wk, then wv, then wo (SPEC-E4-E6.md section 5 step 7).
        let mut h = 0;
        while h < N_HEADS {
            let mut i = 0;
            while i < D_MODEL {
                let mut j = 0;
                while j < D_HEAD {
                    layer.wq[h][i][j] = buf[off] as i8;
                    off += 1;
                    j += 1;
                }
                i += 1;
            }
            h += 1;
        }
        h = 0;
        while h < N_HEADS {
            let mut i = 0;
            while i < D_MODEL {
                let mut j = 0;
                while j < D_HEAD {
                    layer.wk[h][i][j] = buf[off] as i8;
                    off += 1;
                    j += 1;
                }
                i += 1;
            }
            h += 1;
        }
        h = 0;
        while h < N_HEADS {
            let mut i = 0;
            while i < D_MODEL {
                let mut j = 0;
                while j < D_HEAD {
                    layer.wv[h][i][j] = buf[off] as i8;
                    off += 1;
                    j += 1;
                }
                i += 1;
            }
            h += 1;
        }
        h = 0;
        while h < N_HEADS {
            let mut j = 0;
            while j < D_HEAD {
                let mut i2 = 0;
                while i2 < D_MODEL {
                    layer.wo[h][j][i2] = buf[off] as i8;
                    off += 1;
                    i2 += 1;
                }
                j += 1;
            }
            h += 1;
        }
        let mut i = 0;
        while i < D_MODEL {
            let mut m = 0;
            while m < D_MLP {
                layer.win[i][m] = buf[off] as i8;
                off += 1;
                m += 1;
            }
            i += 1;
        }
        let mut m = 0;
        while m < D_MLP {
            layer.bin[m] = read_i64(buf, off);
            off += 8;
            m += 1;
        }
        m = 0;
        while m < D_MLP {
            let mut i = 0;
            while i < D_MODEL {
                layer.wout[m][i] = buf[off] as i8;
                off += 1;
                i += 1;
            }
            m += 1;
        }
        let mut i = 0;
        while i < D_MODEL {
            layer.bout[i] = read_i64(buf, off);
            off += 8;
            i += 1;
        }
        l += 1;
    }
    let mut i = 0;
    while i < D_MODEL {
        let mut v = 0;
        while v < VOCAB {
            out.u[i][v] = buf[off] as i8;
            off += 1;
            v += 1;
        }
        i += 1;
    }
    let mut n = 0;
    while n < 32 {
        out.exp_n[n] = read_i64(buf, off);
        off += 8;
        n += 1;
    }
    let mut b = 0;
    while b < 256 {
        out.exp_2[b] = read_i64(buf, off);
        off += 8;
        b += 1;
    }
    b = 0;
    while b < 256 {
        out.exp_1[b] = read_i64(buf, off);
        off += 8;
        b += 1;
    }
    b = 0;
    while b < 256 {
        out.exp_0[b] = read_i64(buf, off);
        off += 8;
        b += 1;
    }
    off == GLMW_FILE_LEN
}

/// A valid-`load_check`-shape `Weights` with every entry zero and both header
/// fields at 0 (rejected by `load_check` and by every forward guard). The
/// deserializer overwrites every entry, so this is only the resting state of
/// the static below.
pub const ZERO_WEIGHTS: Weights = Weights {
    n_layers: 0,
    vocab_size: 0,
    tok: [[0i8; D_MODEL]; VOCAB],
    pos: [[0i8; D_MODEL]; MAX_SEQ],
    layers: [
        general_engine::LayerWeights {
            wq: [[[0i8; D_HEAD]; D_MODEL]; N_HEADS],
            wk: [[[0i8; D_HEAD]; D_MODEL]; N_HEADS],
            wv: [[[0i8; D_HEAD]; D_MODEL]; N_HEADS],
            wo: [[[0i8; D_MODEL]; D_HEAD]; N_HEADS],
            win: [[0i8; D_MLP]; D_MODEL],
            bin: [0i64; D_MLP],
            wout: [[0i8; D_MODEL]; D_MLP],
            bout: [0i64; D_MODEL],
        },
        general_engine::LayerWeights {
            wq: [[[0i8; D_HEAD]; D_MODEL]; N_HEADS],
            wk: [[[0i8; D_HEAD]; D_MODEL]; N_HEADS],
            wv: [[[0i8; D_HEAD]; D_MODEL]; N_HEADS],
            wo: [[[0i8; D_MODEL]; D_HEAD]; N_HEADS],
            win: [[0i8; D_MLP]; D_MODEL],
            bin: [0i64; D_MLP],
            wout: [[0i8; D_MODEL]; D_MLP],
            bout: [0i64; D_MODEL],
        },
    ],
    u: [[0i8; VOCAB]; D_MODEL],
    exp_n: [0i64; 32],
    exp_2: [0i64; 256],
    exp_1: [0i64; 256],
    exp_0: [0i64; 256],
};

fn tokens_usize() -> [usize; MAX_SEQ] {
    let src = *TOKENS.borrow();
    let mut out = [0usize; MAX_SEQ];
    let mut i = 0;
    while i < MAX_SEQ {
        out[i] = src[i] as usize;
        i += 1;
    }
    out
}

/// Address of the `GLMW` upload buffer, `GLMW_FILE_LEN` bytes long, in linear memory.
#[unsafe(no_mangle)]
#[allow(unsafe_code)]
pub extern "C" fn wasm_get_weight_buf_ptr() -> *const u8 {
    let ptr = BUF.borrow().as_ptr();
    ptr
}

/// Deserializes the upload buffer and runs `general_engine::load_check` on it.
/// Returns 1 and keeps the weights if the file is a valid `GLMW` v1 blob whose
/// every entry is in bounds, 0 otherwise. A failed load also drops the previously
/// accepted weights, so nothing runs on a file that did not pass `load_check`.
#[unsafe(no_mangle)]
#[allow(unsafe_code)]
pub extern "C" fn wasm_load_weights() -> i32 {
    // Parse into the static (no ~480 KB stack frame), then run load_check on it.
    let parsed = {
        let buf = BUF.borrow();
        let mut w = WEIGHTS.borrow_mut();
        parse_glmw_into(&buf, &mut w)
    };
    if parsed && general_engine::load_check(&WEIGHTS.borrow()) {
        *LOADED.borrow_mut() = true;
        1
    } else {
        // A failed load resets to the rejected zero resting state, so nothing
        // runs on a file that did not pass load_check.
        *WEIGHTS.borrow_mut() = ZERO_WEIGHTS;
        *LOADED.borrow_mut() = false;
        0
    }
}

/// Address of the token window, `MAX_SEQ` little-endian `u32` values, in linear memory.
#[unsafe(no_mangle)]
#[allow(unsafe_code)]
pub extern "C" fn wasm_get_tokens_buf_ptr() -> *mut u32 {
    let ptr = TOKENS.borrow_mut().as_mut_ptr();
    ptr
}

/// Greedy next token for the sequence currently in the token buffer.
/// Returns the token, or -1 if the weights or the input are rejected.
#[unsafe(no_mangle)]
#[allow(unsafe_code)]
pub extern "C" fn wasm_predict_next(seq_len: i32) -> i32 {
    if seq_len < 0 || seq_len as usize > MAX_SEQ {
        return -1;
    }
    if !*LOADED.borrow() {
        return -1;
    }
    let tokens = tokens_usize();
    let w = WEIGHTS.borrow();
    match general_engine::predict_next(&w, &tokens, seq_len as usize) {
        Some(t) => t as i32,
        None => -1,
    }
}

/// The raw `i64` logits, scale 2^32, for the sequence in the token buffer.
/// Returns the address of `VOCAB` little-endian `i64` values in linear memory,
/// or 0 if the weights or the input are rejected.
#[unsafe(no_mangle)]
#[allow(unsafe_code)]
pub extern "C" fn wasm_forward_logits(seq_len: i32) -> *const i64 {
    if seq_len < 0 || seq_len as usize > MAX_SEQ {
        return core::ptr::null();
    }
    if !*LOADED.borrow() {
        return core::ptr::null();
    }
    let tokens = tokens_usize();
    let w = WEIGHTS.borrow();
    match general_engine::forward_logits(&w, &tokens, seq_len as usize) {
        Some(logits) => {
            *LOGITS.borrow_mut() = logits;
            LOGITS.borrow().as_ptr()
        }
        None => core::ptr::null(),
    }
}

/// Greedy generation, in place, on the token buffer. Writes the prompt
/// (`prompt_len` `u32` values) first, then appends up to `steps` tokens while the
/// window is not full. Returns the final length, or -1 on a rejected input.
#[unsafe(no_mangle)]
#[allow(unsafe_code)]
pub extern "C" fn wasm_generate_greedy(prompt_len: i32, steps: i32) -> i32 {
    if prompt_len <= 0 || prompt_len as usize > MAX_SEQ || steps < 0 {
        return -1;
    }
    if !*LOADED.borrow() {
        return -1;
    }
    let mut tokens = tokens_usize();
    let w = WEIGHTS.borrow();
    match general_engine::generate_greedy(&w, &mut tokens, prompt_len as usize, steps as usize) {
        Some(len) => {
            let mut i = 0;
            while i < MAX_SEQ {
                TOKENS.borrow_mut()[i] = tokens[i] as u32;
                i += 1;
            }
            len as i32
        }
        None => -1,
    }
}

/// Seeded top-k sampling on the raw `i64` logits (scale 2^32).
///
/// Temperature is the rational `t_num / t_den` (both positive). The weight of a
/// logit `l` within the top k is `exp_fix((max - l) * t_den / t_num)`, the engine's
/// own exponential, so all rounding stays inside the proved tables. The draw is a
/// 64-bit linear congruential generator seeded by `seed`; the same seed always
/// returns the same token. Greedy remains untouched: `wasm_predict_next` and
/// `wasm_generate_greedy` never call this.
#[unsafe(no_mangle)]
#[allow(unsafe_code)]
pub extern "C" fn wasm_sample_topk(seq_len: i32, k: i32, t_num: i32, t_den: i32, seed: i32) -> i32 {
    if seq_len <= 0 || seq_len as usize > MAX_SEQ {
        return -1;
    }
    if k < 1 || t_num < 1 || t_den < 1 || t_num > 4096 || t_den > 4096 {
        return -1;
    }
    if !*LOADED.borrow() {
        return -1;
    }
    let tokens = tokens_usize();
    let w = WEIGHTS.borrow();
    let logits = match general_engine::forward_logits(&w, &tokens, seq_len as usize) {
        Some(l) => l,
        None => return -1,
    };
    let vocab = w.vocab_size;
    let kk = if (k as usize) < vocab {
        k as usize
    } else {
        vocab
    };
    // Selection of the top kk: repeatedly move the strict-first maximum of the
    // remaining suffix to the front. index[0..kk] ends sorted by logit, ties by index.
    let mut index = [0usize; VOCAB];
    let mut v = 0;
    while v < VOCAB {
        index[v] = v;
        v += 1;
    }
    let mut i = 0;
    while i < kk {
        let mut best = i;
        let mut j = i + 1;
        while j < vocab {
            if logits[index[j]] > logits[index[best]] {
                best = j;
            }
            j += 1;
        }
        let tmp = index[i];
        index[i] = index[best];
        index[best] = tmp;
        i += 1;
    }
    // Temperature-scaled unnormalized weights, from the engine's tables.
    let max_logit = logits[index[0]];
    let mut weight = [0i64; VOCAB];
    i = 0;
    while i < kk {
        let delta = (max_logit - logits[index[i]]) * (t_den as i64);
        weight[i] = exp_fix_scaled(&w, delta / (t_num as i64));
        i += 1;
    }
    let mut total = 0i64;
    i = 0;
    while i < kk {
        total += weight[i];
        i += 1;
    }
    if total <= 0 {
        // Cannot happen: index[0] has delta 0, whose weight is EXP_ONE.
        return index[0] as i32;
    }
    // LCG draw in [0, total).
    let mut state = (seed as u64)
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    let draw = (state >> 11) as i64 % total;
    let mut acc = 0i64;
    i = 0;
    while i < kk {
        acc += weight[i];
        if draw < acc {
            return index[i] as i32;
        }
        i += 1;
    }
    index[kk - 1] as i32
}

/// `exp_fix` for a delta already in whole units of 2^32: it shifts up to the
/// internal scale and reads the same tables the engine reads. Whole units at or
/// above `EXP_N_LEN` give 0, exactly as in the engine, so the shift never
/// overflows.
fn exp_fix_scaled(w: &Weights, whole_units: i64) -> i64 {
    if whole_units <= 0 {
        return EXP_ONE;
    }
    if whole_units >= general_engine::EXP_N_LEN {
        return 0;
    }
    let d = whole_units << 32;
    general_engine::exp_fix(w, d)
}
