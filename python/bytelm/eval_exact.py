#!/usr/bin/env python3
"""Exact evaluation of weights/tiny_bytelm_v1.bin: integer engine vs float QAT.

Loads the exported GLMW v1 file and evaluates, on the deterministic validation
split of corpus.txt (the same split train_qat.py uses):

- bits per byte and next-byte argmax accuracy of the exact integer engine
  (numpy int64 batch port of ref_engine, validated logit-for-logit against the
  scalar ref_engine.Engine on sample prompts)
- bits per byte and accuracy of the float QAT forward (the same quantized
  integer weights as floats, real exp, the QAT's inter-layer clamp and 1/256
  grid snap, no fixed-point rounding)
- Pearson correlation between float QAT logits and exact integer logits / 2^32
- input-independent static i64 bounds from the weights alone
- 20 prompt -> completion samples through the exact integer engine

Writes evidence/e5-bytelm/eval_exact.json.
"""

import json
import math
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
import ref_engine as re  # noqa: E402

BIN = ROOT / "weights" / "tiny_bytelm_v1.bin"
OUT = ROOT / "evidence" / "e5-bytelm" / "eval_exact.json"

MAX_LAYERS, VOCAB, MAX_SEQ = 2, 256, 32
D_MODEL, N_HEADS, D_HEAD, D_MLP = 128, 4, 32, 512
EXP_ONE = 1 << 30
ALPHA_ONE = 1 << 24
I64_MAX = (1 << 63) - 1
LOG2 = math.log(2)


# ---------------------------------------------------------------- arrays


def arrays_from_weights(w):
    a = {}
    a["tok"] = np.array(w.tok, dtype=np.int64)
    a["pos"] = np.array(w.pos, dtype=np.int64)
    a["wq"], a["wk"], a["wv"], a["wo"] = [], [], [], []
    a["win"], a["bin"], a["wout"], a["bout"] = [], [], [], []
    for lw in w.layers:
        a["wq"].append(np.array(lw.wq, dtype=np.int64))
        a["wk"].append(np.array(lw.wk, dtype=np.int64))
        a["wv"].append(np.array(lw.wv, dtype=np.int64))
        a["wo"].append(np.array(lw.wo, dtype=np.int64))
        a["win"].append(np.array(lw.win, dtype=np.int64))
        a["bin"].append(np.array(lw.bin, dtype=np.int64))
        a["wout"].append(np.array(lw.wout, dtype=np.int64))
        a["bout"].append(np.array(lw.bout, dtype=np.int64))
    a["u"] = np.array(w.u, dtype=np.int64)
    for name in ("exp_n", "exp_2", "exp_1", "exp_0"):
        a[name] = np.array(getattr(w, name), dtype=np.int64)
    return a


def exp_fix_np(d, a):
    """Vectorized exp_fix of the spec, exact on int64."""
    out = np.where(d <= 0, EXP_ONE, 0)
    live = d > 0
    u = d >> 8
    n = u >> 24
    valid = live & (n < 32)
    ni = np.clip(n, 0, 31)
    b2 = (u >> 16) & 255
    b1 = (u >> 8) & 255
    b0 = u & 255
    e = a["exp_n"][ni]
    e = (e * a["exp_2"][b2]) >> 30
    e = (e * a["exp_1"][b1]) >> 30
    e = (e * a["exp_0"][b0]) >> 30
    return np.where(valid, e, out)


def forward_int(a, n_layers, vocab, tokens):
    """Exact integer forward, batched. tokens (B, T) -> logits (B, vocab).

    All active positions are computed at every layer; the logits read
    position T-1, exactly the output of ref_engine.Engine.forward_logits.
    """
    B, T = tokens.shape
    x = a["tok"][tokens] + a["pos"][:T]
    causal = np.tril(np.ones((T, T), dtype=bool))
    h = None
    for l in range(n_layers):
        final = l + 1 == n_layers
        q = np.einsum("btk,hki->bhti", x, a["wq"][l])
        k = np.einsum("btk,hki->bhti", x, a["wk"][l])
        v = np.einsum("btk,hki->bhti", x, a["wv"][l])
        scores = np.einsum("bhti,bhui->bhtu", q, k)
        sent = np.iinfo(np.int64).min // 4
        masked = np.where(causal, scores, sent)
        smax = masked.max(axis=-1, keepdims=True)
        # difference against the MASKED scores: future positions get the
        # sentinel, so their d is huge and exp_fix returns 0, exactly the
        # causal mask of the spec
        e = exp_fix_np(smax - masked, a)
        den = e.sum(axis=-1, keepdims=True)
        alpha = (e * ALPHA_ONE) // den
        zsum = np.einsum("bhtu,bhui->bthi", alpha, v)
        z = zsum >> 16
        zf = z.reshape(B, T, N_HEADS * D_HEAD)
        wo_flat = a["wo"][l].reshape(N_HEADS * D_HEAD, D_MODEL)
        att = zf @ wo_flat
        r = x * ALPHA_ONE + att
        pre = r @ a["win"][l] + a["bin"][l] * 256
        m = np.where(pre > 0, pre >> 8, 0)
        o = m @ a["wout"][l] + a["bout"][l]
        f = (r * 256 + o) >> 16
        if final:
            h = f[:, -1]
        else:
            xn = f >> 16
            np.clip(xn, -127, 127, out=xn)
            x = xn
    return h @ a["u"][:, :vocab]


def forward_float(a, n_layers, vocab, tokens):
    """Float QAT forward: the same quantized weights as float64, real exp,
    the QAT inter-layer clamp and 1/256 grid snap, no fixed-point rounding."""
    B, T = tokens.shape
    tok = a["tok"] / 256.0
    pos = a["pos"] / 256.0
    wq = [a["wq"][l] / 256.0 for l in range(n_layers)]
    wk = [a["wk"][l] / 256.0 for l in range(n_layers)]
    wv = [a["wv"][l] / 256.0 for l in range(n_layers)]
    wo = [a["wo"][l] / 256.0 for l in range(n_layers)]
    win = [a["win"][l] / 256.0 for l in range(n_layers)]
    binf = [a["bin"][l] / float(2 ** 32) for l in range(n_layers)]
    wout = [a["wout"][l] / 256.0 for l in range(n_layers)]
    bout = [a["bout"][l] / float(2 ** 40) for l in range(n_layers)]
    u = a["u"] / 256.0

    x = tok[tokens] + pos[:T]
    causal = np.tril(np.ones((T, T), dtype=bool))
    h = None
    for l in range(n_layers):
        final = l + 1 == n_layers
        q = np.einsum("btk,hki->bhti", x, wq[l])
        k = np.einsum("btk,hki->bhti", x, wk[l])
        v = np.einsum("btk,hki->bhti", x, wv[l])
        scores = np.einsum("bhti,bhui->bhtu", q, k)
        scores = np.where(causal, scores, -np.inf)
        smax = scores.max(axis=-1, keepdims=True)
        ex = np.exp(scores - smax)
        alpha = ex / ex.sum(axis=-1, keepdims=True)
        z = np.einsum("bhtu,bhui->bthi", alpha, v).reshape(B, T, N_HEADS * D_HEAD)
        att = z @ wo[l].reshape(N_HEADS * D_HEAD, D_MODEL)
        r = x + att
        pre = r @ win[l] + binf[l]
        m = np.maximum(pre, 0.0)
        o = m @ wout[l] + bout[l]
        f = r + o
        if final:
            h = f[:, -1]
        else:
            snapped = np.floor(f * 256.0) / 256.0
            x = np.clip(snapped, -127 / 256.0, 127 / 256.0)
    return h @ u[:, :vocab]


# ---------------------------------------------------------------- static bounds


def static_bounds(w):
    """Input-independent worst case per stage, from the weights alone.

    The stream entering any layer is bounded by 127 (layer 0 by the tok/pos
    boxes, later layers by the inter-layer clamp), positions are at most 32.
    """
    b = {}
    bmax = {}
    bx = 127
    proj = 0
    scores = 0
    zmix = 0
    wout = 0
    batt = [0] * D_MODEL
    for l in range(w.n_layers):
        lw = w.layers[l]
        for h in range(N_HEADS):
            wq, wk, wv = lw.wq[h], lw.wk[h], lw.wv[h]
            bq = [bx * sum(abs(wq[k][i]) for k in range(D_MODEL)) for i in range(D_HEAD)]
            bk = [bx * sum(abs(wk[k][i]) for k in range(D_MODEL)) for i in range(D_HEAD)]
            bv = [bx * sum(abs(wv[k][i]) for k in range(D_MODEL)) for i in range(D_HEAD)]
            proj = max([proj] + bq + bk + bv)
            bs = sum(bq[i] * bk[i] for i in range(D_HEAD))
            scores = max(scores, bs)
            bvmax = max(bv)
            zmix = max(zmix, ALPHA_ONE * bvmax)  # each alpha*v and partial sum
            bz = (ALPHA_ONE * bvmax) >> 16
            wo = lw.wo[h]
            bw = [sum(bz * abs(wo[t][k]) for t in range(D_HEAD)) for k in range(D_MODEL)]
            wout = max([wout] + bw)
            batt = [x + y for x, y in zip(batt, bw)]
    b["project"] = proj
    b["head_scores"] = scores
    b["exp_fix"] = max(2 * scores, EXP_ONE * EXP_ONE)
    b["softmax_weights"] = max(EXP_ONE * ALPHA_ONE, MAX_SEQ * EXP_ONE)
    b["head_output.z"] = zmix
    b["head_output.w"] = wout
    b["attention"] = max(batt)
    br = [bx * ALPHA_ONE + int(batt[k]) for k in range(D_MODEL)]
    b["residual"] = max(br)
    bpre_max = 0
    bm_max = 0
    bo_max = 0
    bfin_max = 0
    blogit = 0
    for l in range(w.n_layers):
        lw = w.layers[l]
        bpre_l = [sum(br[k] * abs(lw.win[k][i]) for k in range(D_MODEL))
                  + abs(lw.bin[i]) * 256 for i in range(D_MLP)]
        bpre_max = max(bpre_max, max(bpre_l))
        bm_l = [(v >> 8) + 1 for v in bpre_l]
        bm_max = max(bm_max, max(bm_l))
        bo_l = [sum(bm_l[i] * abs(lw.wout[i][k]) for i in range(D_MLP))
                + abs(lw.bout[k]) for k in range(D_MODEL)]
        bo_max = max(bo_max, max(bo_l))
        bfin_l = [(br[k] * 256 + bo_l[k]) for k in range(D_MODEL)]
        bfin_max = max(bfin_max, max(bfin_l))
        bfh = [(v >> 16) + 1 for v in bfin_l]
        for vcol in range(w.vocab_size):
            s = 0
            for k in range(D_MODEL):
                s += bfh[k] * abs(w.u[k][vcol])
            blogit = max(blogit, s)
    b["mlp_hidden"] = bpre_max
    b["mlp_output"] = bo_max
    b["final_stream"] = bfin_max
    b["unembed"] = blogit
    return b


# ---------------------------------------------------------------- metrics


def bits_per_byte(logits, targets):
    """logits (N, V) float64 normalized logit units; targets (N,)."""
    m = logits.max(axis=1, keepdims=True)
    ex = np.exp(logits - m)
    p = ex / ex.sum(axis=1, keepdims=True)
    pt = p[np.arange(len(targets)), targets]
    return float(-(np.log(pt) / LOG2).mean())


def argmax_acc(logits, targets):
    return float((logits.argmax(axis=1) == targets).mean())


def load_val_windows():
    lines = (HERE / "corpus.txt").read_text("ascii").split("\n")
    lines = [ln for ln in lines if ln]
    val_lines = [ln for i, ln in enumerate(lines) if i % 10 == 7]
    val_bytes = ("\n".join(val_lines) + "\n").encode("ascii")
    n = len(val_bytes) - (MAX_SEQ + 1) + 1
    data = np.frombuffer(val_bytes, dtype=np.uint8)
    win = np.lib.stride_tricks.sliding_window_view(data, MAX_SEQ + 1)[::4]
    return np.ascontiguousarray(win)


SAMPLE_PROMPTS = [
    b"The capital of France is",
    b"Rome is the capital of",
    b"A stitch in time",
    b"Actions speak louder",
    b"The engine checks",
    b"What is a proof? A proof is",
    b"two plus three is",
    b"The small cat sat on",
    b"Hello. How are you? I am",
    b"Paris is spelled",
    b"Knowledge is",
    b"Better late than",
    b"Two heads are",
    b"The early bird",
    b"Where is the old book? It is",
    b"Monday is a day",
    b"In January the days",
    b"The proof checks each",
    b"Greedy decoding always",
    b"Time heals",
]


def main():
    w = re.load(BIN)
    if not re.load_check(w):
        print("FAIL: load_check is False")
        return 1
    a = arrays_from_weights(w)
    n_layers, vocab = w.n_layers, w.vocab_size

    # -- validate the numpy int path against the scalar reference
    e = re.Engine(w)
    rng = np.random.default_rng(20261120)
    checks = 0
    mismatches = 0
    for _ in range(8):
        T = int(rng.integers(8, 33))
        toks = rng.integers(0, 256, size=(1, T))
        ref = e.forward_logits(toks[0].tolist(), T)
        got = forward_int(a, n_layers, vocab, toks)
        checks += vocab
        mismatches += int(np.sum(np.array(ref) != got[0]))
    print(f"numpy int path vs ref_engine scalar: {checks} logits, "
          f"{mismatches} mismatches")
    assert mismatches == 0, "numpy integer forward disagrees with the reference"

    # -- validation windows
    win = load_val_windows()
    # one shared subset for the head-to-head metrics
    sub = np.ascontiguousarray(win[::8])
    ctx = sub[:, :MAX_SEQ]
    tgt = sub[:, MAX_SEQ].astype(np.int64)
    print(f"val windows: {len(win)} (stride 4), head-to-head subset {len(sub)} (stride 32)")

    # -- float QAT metrics (all windows)
    t0 = time.time()
    float_logits_all = []
    for i in range(0, len(win), 128):
        fl = forward_float(a, n_layers, vocab, win[i:i + 128, :MAX_SEQ])
        float_logits_all.append(fl)
    float_logits_all = np.vstack(float_logits_all)
    tgt_all = win[:, MAX_SEQ].astype(np.int64)
    fbpb_all = bits_per_byte(float_logits_all, tgt_all)
    facc_all = argmax_acc(float_logits_all, tgt_all)
    print(f"float QAT (all {len(win)} windows): bpb {fbpb_all:.4f}, "
          f"argmax acc {facc_all:.4f} ({time.time() - t0:.1f}s)")

    # -- integer metrics (subset), float on the same subset
    t0 = time.time()
    int_logits = []
    for i in range(0, len(sub), 64):
        il = forward_int(a, n_layers, vocab, ctx[i:i + 64])
        int_logits.append(il)
    int_logits = np.vstack(int_logits)
    int_secs = time.time() - t0
    fl_sub = forward_float(a, n_layers, vocab, ctx)
    ibpb = bits_per_byte(int_logits / float(2 ** 32), tgt)
    iacc = argmax_acc(int_logits, tgt)
    fbpb = bits_per_byte(fl_sub, tgt)
    facc = argmax_acc(fl_sub, tgt)
    agree = float((int_logits.argmax(1) == fl_sub.argmax(1)).mean())
    print(f"exact integer (subset): bpb {ibpb:.4f}, argmax acc {iacc:.4f} "
          f"({int_secs:.1f}s for {len(sub)} windows)")
    print(f"float QAT (same subset): bpb {fbpb:.4f}, argmax acc {facc:.4f}")

    # -- logit correlation
    li = int_logits / float(2 ** 32)
    lf = fl_sub
    corr = float(np.corrcoef(li.ravel(), lf.ravel())[0, 1])
    max_abs_diff = float(np.abs(li - lf).max())
    print(f"logit correlation (int/2^32 vs float QAT): {corr:.6f}, "
          f"max |diff| {max_abs_diff:.3e}")

    # -- static bounds
    bounds = static_bounds(w)
    print("static bounds from the weights alone:")
    ok_bounds = True
    for name, v in bounds.items():
        fits = v <= I64_MAX
        ok_bounds &= fits
        print(f"  {name:18s} <= {v:>24d}  {int(v).bit_length():2d} bits  "
              f"{'fits i64' if fits else 'EXCEEDS i64'}")
    assert ok_bounds, "a stage can exceed i64"

    # -- 20 samples through the exact integer engine
    samples = []
    for prompt in SAMPLE_PROMPTS:
        buf = e.generate_greedy(list(prompt), MAX_SEQ)
        assert buf is not None
        completion = bytes(buf[len(prompt):])
        samples.append({
            "prompt": prompt.decode("ascii"),
            "completion": completion.decode("ascii", "replace"),
            "full": bytes(buf).decode("ascii", "replace"),
        })
    for s in samples:
        print(f"  {s['prompt']!r} -> {s['completion']!r}")

    result = dict(
        bin=str(BIN.relative_to(ROOT)),
        bin_bytes=BIN.stat().st_size,
        load_check=True,
        numpy_int_vs_ref_mismatches=mismatches,
        val_windows=len(win),
        head_to_head_windows=len(sub),
        float_qat=dict(bits_per_byte_all=round(fbpb_all, 4),
                       argmax_acc_all=round(facc_all, 4),
                       bits_per_byte_subset=round(fbpb, 4),
                       argmax_acc_subset=round(facc, 4)),
        integer_engine=dict(bits_per_byte=round(ibpb, 4),
                            argmax_acc=round(iacc, 4),
                            numpy_seconds=round(int_secs, 1)),
        argmax_agreement=round(agree, 4),
        logit_correlation=round(corr, 6),
        logit_max_abs_diff=max_abs_diff,
        static_bounds={k: int(v) for k, v in bounds.items()},
        static_bounds_max_bits=max(int(v).bit_length() for v in bounds.values()),
        samples=samples,
    )
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print(f"wrote {OUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
