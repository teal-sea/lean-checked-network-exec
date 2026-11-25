#!/usr/bin/env python3
"""Train the tiny 2-layer byte-level LM with quantization-aware training (QAT).

CPU only, 2 threads, hard wall-clock budget. The trained model is exported to
`weights/tiny_bytelm_v1.bin` in the exact GLMW v1 format of SPEC-E4-E6.md.

QAT design (normalized units). Divide every integer quantity by its scale and
the engine becomes a standard float transformer:

    integer value at scale 2^s  ->  float v / 2^s

    x   = tok + pos            (2^8)    ->  x_hat  in [-0.5, 0.5]
    q   = x . wq               (2^16)   ->  q_hat  = x_hat . (wq / 256)
    s   = q . k                (2^32)   ->  s_hat  = q_hat . k_hat
    alpha = e . 2^24 / den              ->  softmax(s_hat)   (exact exp; the
                                            exp tables round it by <= 2^-30)
    z   = (sum alpha v) >> 16  (2^24)   ->  z_hat  = sum alpha_hat v_hat
    att = z . wo               (2^32)   ->  att_hat = z_hat . (wo / 256)
    r   = x * 2^24 + att       (2^32)   ->  r_hat  = x_hat + att_hat
    pre = r . win + bin * 2^8  (2^40)   ->  pre_hat = r_hat . (win/256) + bin/2^32
    m   = relu(pre) >> 8       (2^32)   ->  m_hat  = relu(pre_hat)
    o   = m . wout + bout      (2^40)   ->  o_hat  = m_hat . (wout/256) + bout/2^40
    f   = (r * 2^8 + o) >> 16  (2^24)   ->  f_hat  = r_hat + o_hat
    x_next = clamp(f >> 16, +/-127)    ->  clamp(snap(f_hat, 1/256), +/-127/256)
    logits = f . u             (2^32)   ->  logits_hat = f_hat . (u / 256)

STE (straight-through estimator) is applied at every quantization point:

- every i8 matrix:  q = clamp(round(w_hat * 256), box) / 256
- bin:              q = clamp(round(b_hat * 2^32), 2^30) / 2^32
- bout:             q = clamp(round(b_hat * 2^40), 2^37) / 2^40
- inter-layer:      clamp(snap(f_hat)) as above

The boxes are exactly the load_check ranges of SPEC-E4-E6.md, so the exported
integer weights always pass load_check with zero out-of-range coordinates.

The exponential tables of the exported file are the exact rational tables of
scripts/gen_transformer_weights.py (copied verbatim, asserted in range).

Usage: train_qat.py [--budget-seconds N] (default 400, hard cap below 8 min)
"""

import os
import sys
import time

for var in ("OMP_NUM_THREADS", "MKL_NUM_THREADS", "OPENBLAS_NUM_THREADS",
            "TORCH_NUM_THREADS"):
    os.environ.setdefault(var, "2")

import torch  # noqa: E402
import torch.nn as nn  # noqa: E402
import torch.nn.functional as F  # noqa: E402

torch.set_num_threads(2)

from pathlib import Path  # noqa: E402

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "scripts"))
import ref_engine as re  # noqa: E402
import gen_transformer_weights as gen  # noqa: E402

# load_check boxes (SPEC-E4-E6.md section 3), in integer units.
BOX = dict(tok=68, pos=59, wq=5, wk=22, wv=106, wo=93, win=82, wout=74, u=37)
BIN_BOX = 1 << 30
BOUT_BOX = 1 << 37
I8_SCALE = 256
BIN_SCALE = float(2 ** 32)
BOUT_SCALE = float(2 ** 40)
STREAM_MAX = 127 / 256

D_MODEL, N_HEADS, D_HEAD, D_MLP, MAX_SEQ, VOCAB = 128, 4, 32, 512, 32, 256


def quant(param: torch.Tensor, scale: float, box: int) -> torch.Tensor:
    """STE: forward uses clamp(round(param*scale), box)/scale, backward is identity."""
    q = (torch.round(param * scale) / scale).clamp(-box / scale, box / scale)
    return param + (q - param).detach()


def clamp_snap(f: torch.Tensor) -> torch.Tensor:
    """STE for the inter-layer rescale: clamp(snap(f_hat, 1/256), +/-127/256).

    The integer engine computes x_next = clamp(f >> 16, +/-127) with f an
    integer at scale 2^24, which in normalized units is exactly
    clamp(floor(f_hat * 256) / 256, +/-127/256).
    """
    snapped = ((f * 256).floor() / 256).clamp(-STREAM_MAX, STREAM_MAX)
    return f + (snapped - f).detach()


class QATLayer(nn.Module):
    """One layer. `scale` shrinks layer 0's init: the inter-layer rescale
    clamps the layer-0 stream to +/-127/256, so layer 0 must stay gentle
    (small attention and MLP output) or the clamp collapses the stream to
    sign bits. Layer 1's output is unclamped and carries the full load, like
    the one-layer mod-113 model the boxes come from."""

    def __init__(self, g, scale=1.0):
        super().__init__()

        def u(shape, max_int):
            return nn.Parameter(
                (torch.rand(shape, generator=g) * 2 - 1) * (max_int * scale / 256))

        self.wq = u((N_HEADS, D_MODEL, D_HEAD), 2)    # 1/sqrt(32) folded small
        self.wk = u((N_HEADS, D_MODEL, D_HEAD), 8)
        self.wv = u((N_HEADS, D_MODEL, D_HEAD), 40)
        self.wo = u((N_HEADS, D_HEAD, D_MODEL), 30)
        self.win = u((D_MODEL, D_MLP), 30)
        self.bin = nn.Parameter(torch.zeros(D_MLP))
        self.wout = u((D_MLP, D_MODEL), 25)
        self.bout = nn.Parameter(torch.zeros(D_MODEL))

    def qparams(self):
        return dict(
            wq=quant(self.wq, I8_SCALE, BOX["wq"]),
            wk=quant(self.wk, I8_SCALE, BOX["wk"]),
            wv=quant(self.wv, I8_SCALE, BOX["wv"]),
            wo=quant(self.wo, I8_SCALE, BOX["wo"]),
            win=quant(self.win, I8_SCALE, BOX["win"]),
            bin=quant(self.bin, BIN_SCALE, BIN_BOX),
            wout=quant(self.wout, I8_SCALE, BOX["wout"]),
            bout=quant(self.bout, BOUT_SCALE, BOUT_BOX),
        )


class QATModel(nn.Module):
    """2-layer byte LM, n_heads 4, d_model 128, d_mlp 512: 464,128 parameters."""

    def __init__(self, seed=20261120):
        super().__init__()
        g = torch.Generator().manual_seed(seed)
        self.tok = nn.Parameter((torch.rand((VOCAB, D_MODEL), generator=g) * 2 - 1) * (50 / 256))
        self.pos = nn.Parameter((torch.rand((MAX_SEQ, D_MODEL), generator=g) * 2 - 1) * (40 / 256))
        self.layers = nn.ModuleList([QATLayer(g, 0.25), QATLayer(g, 1.0)])
        self.u_emb = nn.Parameter((torch.rand((D_MODEL, VOCAB), generator=g) * 2 - 1) * (20 / 256))

    def forward(self, idx: torch.Tensor):
        """idx (B, T) byte ids -> (logits (B, T, 256), saturation penalty).

        The penalty is the linear excess of the inter-layer stream beyond the
        clamp range +/-127/256 (linear so its gradient is bounded: a squared
        penalty diverged). It changes no forward value (the clamp is still
        applied exactly); it only adds gradient pressure that keeps the
        layer-0 output inside the range the integer engine can carry, so the
        inter-layer rescale does not collapse the stream to sign bits.
        """
        B, T = idx.shape
        x = quant(self.tok, I8_SCALE, BOX["tok"])[idx] + \
            quant(self.pos, I8_SCALE, BOX["pos"])[:T]
        n_layers = len(self.layers)
        h = None
        penalty = torch.zeros((), device=idx.device)
        for l, layer in enumerate(self.layers):
            final = (l + 1 == n_layers)
            qp = layer.qparams()
            wq = qp["wq"].permute(1, 0, 2).reshape(D_MODEL, N_HEADS * D_HEAD)
            wk = qp["wk"].permute(1, 0, 2).reshape(D_MODEL, N_HEADS * D_HEAD)
            wv = qp["wv"].permute(1, 0, 2).reshape(D_MODEL, N_HEADS * D_HEAD)
            wo = qp["wo"].reshape(N_HEADS * D_HEAD, D_MODEL)
            q = (x @ wq).view(B, T, N_HEADS, D_HEAD)
            k = (x @ wk).view(B, T, N_HEADS, D_HEAD)
            v = (x @ wv).view(B, T, N_HEADS, D_HEAD)
            scores = torch.einsum("bthi,buhi->bhtu", q, k)
            causal = torch.ones(T, T, dtype=torch.bool, device=idx.device).tril()
            scores = scores.masked_fill(~causal, float("-inf"))
            alpha = scores.softmax(dim=-1)
            z = torch.einsum("bhtu,buhi->bthi", alpha, v).reshape(B, T, N_HEADS * D_HEAD)
            att = z @ wo
            r = x + att
            m = F.relu(r @ qp["win"] + qp["bin"])
            o = m @ qp["wout"] + qp["bout"]
            f = r + o
            if final:
                h = f
            else:
                penalty = penalty + F.relu(f.abs() - STREAM_MAX).mean()
                x = clamp_snap(f)
        return h @ quant(self.u_emb, I8_SCALE, BOX["u"]), penalty

    # ------------------------------------------------------------ export

    def export_weights(self) -> "re.Weights":
        """The exact integer model: every coordinate clamped into its box."""

        def ints(param, box, scale):
            return (param.detach().double() * scale).round().clamp(-box, box) \
                .to(torch.int64).tolist()

        tok = ints(self.tok, BOX["tok"], I8_SCALE)
        pos = ints(self.pos, BOX["pos"], I8_SCALE)
        u = ints(self.u_emb, BOX["u"], I8_SCALE)
        layers = []
        for layer in self.layers:
            layers.append(re.LayerWeights(
                ints(layer.wq, BOX["wq"], I8_SCALE),
                ints(layer.wk, BOX["wk"], I8_SCALE),
                ints(layer.wv, BOX["wv"], I8_SCALE),
                ints(layer.wo, BOX["wo"], I8_SCALE),
                ints(layer.win, BOX["win"], I8_SCALE),
                ints(layer.bin, BIN_BOX, BIN_SCALE),
                ints(layer.wout, BOX["wout"], I8_SCALE),
                ints(layer.bout, BOUT_BOX, BOUT_SCALE),
            ))
        tabs = gen.exp_tables()
        exp_n = [int(v) for v in tabs["EXP_N"]]
        exp_2 = [int(v) for v in tabs["EXP_2"]]
        exp_1 = [int(v) for v in tabs["EXP_1"]]
        exp_0 = [int(v) for v in tabs["EXP_0"]]
        for tab in (exp_n, exp_2, exp_1, exp_0):
            assert all(0 <= v <= (1 << 30) for v in tab), "exp table out of range"
        return re.Weights(2, VOCAB, tok, pos, layers, u, exp_n, exp_2, exp_1, exp_0)

    def param_count(self) -> int:
        return sum(p.numel() for p in self.parameters())


# ---------------------------------------------------------------- data


def load_data():
    """Deterministic line split of corpus.txt: every 10th line (index % 10 == 7)
    is validation, the rest is training."""
    lines = (HERE / "corpus.txt").read_text("ascii").split("\n")
    lines = [ln for ln in lines if ln]
    val_lines = [ln for i, ln in enumerate(lines) if i % 10 == 7]
    train_lines = [ln for i, ln in enumerate(lines) if i % 10 != 7]
    train_bytes = ("\n".join(train_lines) + "\n").encode("ascii")
    val_bytes = ("\n".join(val_lines) + "\n").encode("ascii")
    return train_bytes, val_bytes


def windows(data: bytes, length: int = MAX_SEQ + 1):
    """All byte windows of `length` as an int64 tensor (N, length)."""
    t = torch.frombuffer(bytearray(data), dtype=torch.uint8)
    return t.unfold(0, length, 1).long().contiguous()


# ---------------------------------------------------------------- training


def main():
    ap = __import__("argparse").ArgumentParser()
    ap.add_argument("--budget-seconds", type=int, default=400)
    ap.add_argument("--batch", type=int, default=64)
    ap.add_argument("--max-steps", type=int, default=4000)
    ap.add_argument("--lr", type=float, default=2e-3)
    ap.add_argument("--out", type=Path, default=ROOT / "weights" / "tiny_bytelm_v1.bin")
    args = ap.parse_args()

    t_start = time.time()
    torch.manual_seed(20261120)

    train_bytes, val_bytes = load_data()
    train_win = windows(train_bytes)
    val_win = windows(val_bytes)[::4].contiguous()  # stride 4, fixed
    print(f"corpus: train {len(train_bytes)} B ({len(train_win)} windows), "
          f"val {len(val_bytes)} B ({len(val_win)} windows)", flush=True)

    model = QATModel()
    n_params = model.param_count()
    print(f"model: 2 layers, {n_params} parameters", flush=True)

    # weight decay keeps the master weights inside their boxes (the
    # cross-entropy arms race otherwise drives every matrix to its clamp and
    # the value path amplifies attention to ~2^42). Embeddings and biases are
    # exempt (standard no-decay group). Layer 0 learns at 0.15x: it must stay
    # gentle for the inter-layer clamp, so it moves slowly from a small init.
    decay, no_decay, layer0 = [], [], []
    for name, p in model.named_parameters():
        if name.startswith("layers.0."):
            layer0.append(p)
        elif name.split(".")[-1] in ("bin", "bout") or name in ("tok", "pos"):
            no_decay.append(p)
        else:
            decay.append(p)
    opt = torch.optim.AdamW(
        [
            {"params": layer0, "lr": args.lr * 0.15, "weight_decay": 0.02},
            {"params": decay, "lr": args.lr, "weight_decay": 0.02},
            {"params": no_decay, "lr": args.lr, "weight_decay": 0.0},
        ],
        betas=(0.9, 0.95),
    )
    warmup = 100
    planned = args.max_steps

    def lr_lambda(step):
        if step < warmup:
            return (step + 1) / warmup
        t = (step - warmup) / max(1, planned - warmup)
        return 0.1 + 0.9 * 0.5 * (1 + __import__("math").cos(__import__("math").pi * t))

    sched = torch.optim.lr_scheduler.LambdaLR(opt, lr_lambda)

    g = torch.Generator().manual_seed(20261120)
    step = 0
    ema_loss = None
    ema_penalty = None
    log = []
    while step < args.max_steps:
        if time.time() - t_start > args.budget_seconds:
            break
        idx = train_win[torch.randint(len(train_win), (args.batch,), generator=g)]
        logits, penalty = model(idx[:, :-1])
        loss = F.cross_entropy(logits.reshape(-1, VOCAB), idx[:, 1:].reshape(-1))
        opt.zero_grad(set_to_none=True)
        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
        opt.step()
        sched.step()
        step += 1
        ema_loss = loss.item() if ema_loss is None else 0.98 * ema_loss + 0.02 * loss.item()
        ema_penalty = penalty.item() if ema_penalty is None \
            else 0.98 * ema_penalty + 0.02 * penalty.item()
        if step % 50 == 0 or step == 1:
            dt = time.time() - t_start
            line = (f"step {step:5d}  loss {loss.item():.4f}  ema {ema_loss:.4f}  "
                    f"bpb {ema_loss / __import__('math').log(2):.3f}  "
                    f"satur {ema_penalty:.3g}  {dt:.0f}s")
            print(line, flush=True)
            log.append(line)

    train_secs = time.time() - t_start

    # ---- validation bits per byte, float QAT forward, no grad
    model.eval()
    with torch.no_grad():
        tot_nll, tot_bytes = 0.0, 0
        for i in range(0, len(val_win), 256):
            batch = val_win[i:i + 256]
            logits, _ = model(batch[:, :-1])
            nll = F.cross_entropy(logits.reshape(-1, VOCAB), batch[:, 1:].reshape(-1),
                                  reduction="sum")
            tot_nll += nll.item()
            tot_bytes += batch[:, 1:].numel()
        val_bpb_float = tot_nll / tot_bytes / __import__("math").log(2)
    print(f"val bits/byte (float QAT): {val_bpb_float:.4f}", flush=True)

    # ---- weight saturation report (mean |integer weight| per matrix vs box)
    sat = {}
    with torch.no_grad():
        for l, layer in enumerate(model.layers):
            for name, box in BOX.items():
                if name in ("tok", "pos", "u"):
                    continue
                p = getattr(layer, name)
                mean_abs = (p.detach().double() * 256).round().clamp(-box, box).abs().mean().item()
                sat[f"l{l}.{name}"] = [round(mean_abs, 2), box]
        for name in ("tok", "pos", "u"):
            p = getattr(model, "u_emb" if name == "u" else name)
            mean_abs = (p.detach().double() * 256).round().clamp(-BOX[name], BOX[name]).abs().mean().item()
            sat[name] = [round(mean_abs, 2), BOX[name]]
    print(f"weight saturation (mean |int| / box): "
          f"{ {k: f'{v[0]}/{v[1]}' for k, v in sat.items()} }", flush=True)

    # ---- export
    w = model.export_weights()
    if not re.load_check(w):
        print("FAIL: exported weights do not pass load_check", file=sys.stderr)
        return 1
    args.out.parent.mkdir(parents=True, exist_ok=True)
    re.save(w, args.out)
    data = args.out.read_bytes()
    w2 = re.load(args.out)
    print(f"exported {args.out} ({len(data)} bytes), round-trip load_check "
          f"{re.load_check(w2)}", flush=True)

    result = dict(
        n_params=n_params,
        steps=step,
        train_seconds=round(train_secs, 1),
        final_ema_train_loss=round(ema_loss, 4),
        final_ema_saturation_penalty=round(ema_penalty, 6),
        val_bits_per_byte_float_qat=round(val_bpb_float, 4),
        weight_saturation=sat,
        corpus_train_bytes=len(train_bytes),
        corpus_val_bytes=len(val_bytes),
        batch=args.batch,
        lr=args.lr,
        log=log,
    )
    out_json = ROOT / "evidence" / "e5-bytelm" / "train_result.json"
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(__import__("json").dumps(result, indent=2) + "\n")
    print(f"wrote {out_json.relative_to(ROOT)}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
