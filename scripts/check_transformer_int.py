#!/usr/bin/env python3
"""Python reference of rust/transformer: the same fixed-width program, on Python integers.

Standard library only. Python integers do not overflow, so this script can measure how wide
every number of the program gets, which the Rust cannot do for itself.

What it does, in order:

1. Loads the checkpoint through gen_transformer_weights.py and checks that
   rust/transformer/src/weights.rs on disk is byte for byte what the generator emits. The Python
   reference and the Rust therefore read the same integers.
2. Computes an input-independent worst-case bound for every stage from the weights alone, and
   checks each against the i64 range.
3. Runs the program on all 12,769 pairs. Records the largest absolute value of every stage's
   output, of every product and of every partial sum, the wrong answers, the ties and the
   smallest margin (the right logit minus the largest other logit).
4. Writes rust/transformer/tests/fixtures/python_reference.txt (an FNV-1a 64 hash of all
   logits, the smallest margin and its pair), which `cargo test` compares with the Rust.
5. Unless --no-rust: runs `cargo run --release --example dump_logits` and compares every logit
   of every pair with the reference.
6. With --parent DIR (a lean-checked-network checkout) and numpy importable: checks the
   quantised integers against int_transformer.py quantise(W, 8), the attention scores against
   its build_tables, and the logits against a float64 forward pass of the quantised model.
7. Writes evidence/transformer-int/summary.txt. Exits nonzero if any check fails.

Usage:
  check_transformer_int.py CHECKPOINT.npz [--parent DIR] [--no-rust] [--no-partials] [--rows N]

  --no-partials  skip the products and partial sums (about three times faster)
  --rows N       only the first N values of a. A partial run writes no fixture and no evidence
"""

import argparse
import hashlib
import itertools
import operator
import platform
import struct
import subprocess
import sys
import time
from pathlib import Path

sys.dont_write_bytecode = True  # no scripts/__pycache__ in the repository
sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_transformer_weights as gen  # noqa: E402

ROOT = gen.ROOT
CRATE = ROOT / "rust" / "transformer"
WEIGHTS_RS = CRATE / "src" / "weights.rs"
LIB_RS = CRATE / "src" / "lib.rs"
FIXTURE = CRATE / "tests" / "fixtures" / "python_reference.txt"
SUMMARY = ROOT / "evidence" / "transformer-int" / "summary.txt"

P, VOCAB, EQ = 113, 114, 113
N_POS, D_MODEL, N_HEADS, D_HEAD, D_MLP = 3, 128, 4, 32, 512
EXP_FRAC_BITS = gen.EXP_FRAC_BITS
EXP_ONE = 1 << EXP_FRAC_BITS
EXP_N_LEN = gen.EXP_N_LEN
ALPHA_ONE = 1 << 24
I64_MAX = (1 << 63) - 1

# The stages, in program order, with the scale of each stage's output.
STAGES = [
    ("embed", "x = TOK[tok] + POS[pos]", "2^8"),
    ("project", "query, key and value vectors", "2^16"),
    ("head_scores", "s = q . k", "2^32"),
    ("exp_fix", "d = max(s) - s, table products, e", "2^30"),
    ("softmax_weights", "e * 2^24, e0 + e1 + e2, alpha", "2^24"),
    ("head_output.z", "alpha * v, their sum, z after >> 16", "2^24"),
    ("head_output.w", "z * WO", "2^32"),
    ("attention", "running sum of the four heads", "2^32"),
    ("residual", "x2 * 2^24, r", "2^32"),
    ("mlp_hidden", "r * WIN, BIN * 2^8, pre, m after >> 8", "2^32"),
    ("mlp_output", "m * WOUT, o", "2^40"),
    ("final_stream", "r * 2^8, r * 2^8 + o, fin after >> 16", "2^24"),
    ("unembed", "fin * U, logits", "2^32"),
]


class Stats:
    """Largest absolute value seen per stage: stage outputs, and products and partial sums."""

    def __init__(self, partials):
        self.partials = partials
        self.out = {name: 0 for name, _, _ in STAGES}
        self.inner = {name: 0 for name, _, _ in STAGES}

    def value(self, stage, v):
        a = -v if v < 0 else v
        if a > self.out[stage]:
            self.out[stage] = a

    def values(self, stage, vs):
        a = max(max(vs), -min(vs))
        if a > self.out[stage]:
            self.out[stage] = a

    def step(self, stage, v):
        a = -v if v < 0 else v
        if a > self.inner[stage]:
            self.inner[stage] = a

    def dot(self, stage, xs, ws):
        """sum of xs[k] * ws[k], k ascending from 0, as the Rust loops accumulate."""
        if not self.partials:
            return sum(map(operator.mul, xs, ws))
        products = list(map(operator.mul, xs, ws))
        total, lo, hi = 0, 0, 0
        for acc in itertools.accumulate(products):
            if acc < lo:
                lo = acc
            elif acc > hi:
                hi = acc
            total = acc
        a = max(max(products), -min(products), hi, -lo)
        if a > self.inner[stage]:
            self.inner[stage] = a
        return total


class Model:
    """The program of rust/transformer/src/lib.rs, stage by stage."""

    def __init__(self, tables, stats):
        self.t = tables
        self.stats = stats
        t = tables
        # Columns, so that each dot product reads one contiguous list.
        self.wq_cols = [[[t["WQ"][h][k][i] for k in range(D_MODEL)] for i in range(D_HEAD)] for h in range(N_HEADS)]
        self.wk_cols = [[[t["WK"][h][k][i] for k in range(D_MODEL)] for i in range(D_HEAD)] for h in range(N_HEADS)]
        self.wv_cols = [[[t["WV"][h][k][i] for k in range(D_MODEL)] for i in range(D_HEAD)] for h in range(N_HEADS)]
        self.wo_cols = [[[t["WO"][h][i][k] for i in range(D_HEAD)] for k in range(D_MODEL)] for h in range(N_HEADS)]
        self.win_cols = [[t["Win"][k][i] for k in range(D_MODEL)] for i in range(D_MLP)]
        self.wout_cols = [[t["Wout"][i][k] for i in range(D_MLP)] for k in range(D_MODEL)]
        self.u_cols = [[t["U"][k][c] for k in range(D_MODEL)] for c in range(P)]
        # embed, project and head_scores depend on (head, position, token) only. Each is computed
        # once and reused across pairs; the values are the ones the Rust recomputes per call.
        self._x = {}
        self._q = {}
        self._key = {}
        self._val = {}
        self._score = {}

    def embed(self, tok, pos):
        got = self._x.get((tok, pos))
        if got is None:
            t = self.t
            got = [t["tok"][tok][k] + t["pos"][pos][k] for k in range(D_MODEL)]
            self.stats.values("embed", got)
            self._x[(tok, pos)] = got
        return got

    def project(self, x, cols):
        out = [self.stats.dot("project", x, col) for col in cols]
        self.stats.values("project", out)
        return out

    def query(self, h):
        got = self._q.get(h)
        if got is None:
            got = self._q[h] = self.project(self.embed(EQ, 2), self.wq_cols[h])
        return got

    def key(self, h, tok, pos):
        got = self._key.get((h, tok, pos))
        if got is None:
            got = self._key[(h, tok, pos)] = self.project(self.embed(tok, pos), self.wk_cols[h])
        return got

    def val(self, h, tok, pos):
        got = self._val.get((h, tok, pos))
        if got is None:
            got = self._val[(h, tok, pos)] = self.project(self.embed(tok, pos), self.wv_cols[h])
        return got

    def score(self, h, tok, pos):
        got = self._score.get((h, tok, pos))
        if got is None:
            got = self.stats.dot("head_scores", self.query(h), self.key(h, tok, pos))
            self.stats.value("head_scores", got)
            self._score[(h, tok, pos)] = got
        return got

    def exp_fix(self, d):
        st = self.stats
        st.step("exp_fix", d)
        if d <= 0:
            st.value("exp_fix", EXP_ONE)
            return EXP_ONE
        u = d >> 8
        n = u >> 24
        if n >= EXP_N_LEN:
            return 0
        t = self.t
        e = t["EXP_N"][n]
        for table, b in (("EXP_2", (u >> 16) & 255), ("EXP_1", (u >> 8) & 255), ("EXP_0", u & 255)):
            prod = e * t[table][b]
            st.step("exp_fix", prod)
            e = prod >> EXP_FRAC_BITS
        st.value("exp_fix", e)
        return e

    def softmax_weights(self, s):
        st = self.stats
        smax = s[0]
        for j in range(1, N_POS):
            if s[j] > smax:
                smax = s[j]
        e = [0] * N_POS
        den = 0
        for j in range(N_POS):
            e[j] = self.exp_fix(smax - s[j])
            den += e[j]
            st.step("softmax_weights", den)
        alpha = [0] * N_POS
        for j in range(N_POS):
            num = e[j] * ALPHA_ONE
            st.step("softmax_weights", num)
            alpha[j] = num // den  # both operands are >= 0 and den > 0: Rust's `/` agrees
        st.values("softmax_weights", alpha)
        return alpha, den

    def head_output(self, h, toks, alpha):
        st = self.stats
        v0, v1, v2 = (self.val(h, toks[j], j) for j in range(N_POS))
        a0, a1, a2 = alpha
        z = [0] * D_HEAD
        if st.partials:
            for i in range(D_HEAD):
                t0, t1, t2 = a0 * v0[i], a1 * v1[i], a2 * v2[i]
                p1 = t0 + t1
                p2 = p1 + t2
                for v in (t0, t1, t2, p1, p2):
                    st.step("head_output.z", v)
                z[i] = p2 >> 16
        else:
            for i in range(D_HEAD):
                z[i] = (a0 * v0[i] + a1 * v1[i] + a2 * v2[i]) >> 16
        st.values("head_output.z", z)
        w = [st.dot("head_output.w", z, col) for col in self.wo_cols[h]]
        st.values("head_output.w", w)
        return w

    def forward(self, a, b):
        st = self.stats
        toks = (a, b, EQ)
        att = [0] * D_MODEL
        dens = []
        for h in range(N_HEADS):
            s = [self.score(h, toks[j], j) for j in range(N_POS)]
            alpha, den = self.softmax_weights(s)
            dens.append(den)
            w = self.head_output(h, toks, alpha)
            att = list(map(operator.add, att, w))
            st.values("attention", att)
        x2 = self.embed(EQ, 2)
        lift = [v * ALPHA_ONE for v in x2]
        r = list(map(operator.add, lift, att))
        st.values("residual", lift)
        st.values("residual", r)
        t = self.t
        m = [0] * D_MLP
        for i in range(D_MLP):
            acc = st.dot("mlp_hidden", r, self.win_cols[i])
            bias = t["bin"][i] * 256
            pre = acc + bias
            st.step("mlp_hidden", bias)
            st.step("mlp_hidden", pre)
            if pre > 0:
                m[i] = pre >> 8
        st.values("mlp_hidden", m)
        o = [st.dot("mlp_output", m, self.wout_cols[k]) + t["bout"][k] for k in range(D_MODEL)]
        st.values("mlp_output", o)
        fin = [0] * D_MODEL
        for k in range(D_MODEL):
            up = r[k] * 256
            tot = up + o[k]
            st.step("final_stream", up)
            st.step("final_stream", tot)
            fin[k] = tot >> 16
        st.values("final_stream", fin)
        out = [st.dot("unembed", fin, col) for col in self.u_cols]
        st.values("unembed", out)
        return out, dens


def argmax_first(values):
    best, best_value = 0, values[0]
    for c in range(1, len(values)):
        if values[c] > best_value:
            best_value, best = values[c], c
    return best


# ----------------------------------------------------------------------------------------------
# input-independent bounds


def static_bounds(t):
    """A bound on the absolute value of everything each stage computes, from the weights alone.

    Each bound is a sum of absolute values, so it also bounds every product and every partial
    sum of the stage. Token ranges: positions 0 and 1 hold a token below 113, position 2 holds
    `=`. The softmax weights are at most 2^24 each and at most 2^24 in total.
    """
    b = {}
    bx = [
        [max(abs(t["tok"][tok][k] + t["pos"][j][k]) for tok in range(P)) for k in range(D_MODEL)]
        for j in (0, 1)
    ]
    bx.append([abs(t["tok"][EQ][k] + t["pos"][2][k]) for k in range(D_MODEL)])
    b["embed"] = max(max(row) for row in bx)

    def through(bound, weights, n_out, n_in, at):
        return [sum(bound[k] * abs(at(weights, k, i)) for k in range(n_in)) for i in range(n_out)]

    proj, scores, zmix, wout = 0, 0, 0, 0
    b_att = [0] * D_MODEL
    for h in range(N_HEADS):
        at_kd = lambda w, k, i: w[h][k][i]
        bq = through(bx[2], t["WQ"], D_HEAD, D_MODEL, at_kd)
        bk = [through(bx[j], t["WK"], D_HEAD, D_MODEL, at_kd) for j in range(N_POS)]
        bv = [through(bx[j], t["WV"], D_HEAD, D_MODEL, at_kd) for j in range(N_POS)]
        proj = max([proj, max(bq)] + [max(v) for v in bk] + [max(v) for v in bv])
        bs = [sum(bq[i] * bk[j][i] for i in range(D_HEAD)) for j in range(N_POS)]
        scores = max(scores, max(bs))
        bvmax = [max(bv[j][i] for j in range(N_POS)) for i in range(D_HEAD)]
        # each alpha[j] * v[j][i] and each partial sum is at most (alpha0 + alpha1 + alpha2) * max |v|
        zmix = max(zmix, ALPHA_ONE * max(bvmax))
        bz = [(ALPHA_ONE * v) >> 16 for v in bvmax]
        bw = [sum(bz[i] * abs(t["WO"][h][i][k]) for i in range(D_HEAD)) for k in range(D_MODEL)]
        wout = max(wout, max(bw))
        b_att = [x + y for x, y in zip(b_att, bw)]
    b["project"] = proj
    b["head_scores"] = scores
    # d = max(s) - s is at most twice the score bound; a table product is at most 2^30 * 2^30
    b["exp_fix"] = max(2 * scores, EXP_ONE * EXP_ONE)
    b["softmax_weights"] = max(EXP_ONE * ALPHA_ONE, N_POS * EXP_ONE)
    b["head_output.z"] = zmix
    b["head_output.w"] = wout
    b["attention"] = max(b_att)
    b_r = [bx[2][k] * ALPHA_ONE + b_att[k] for k in range(D_MODEL)]
    b["residual"] = max(b_r)
    b_pre = [
        sum(b_r[k] * abs(t["Win"][k][i]) for k in range(D_MODEL)) + abs(t["bin"][i]) * 256
        for i in range(D_MLP)
    ]
    b["mlp_hidden"] = max(b_pre)
    b_m = [v >> 8 for v in b_pre]
    b_o = [sum(b_m[i] * abs(t["Wout"][i][k]) for i in range(D_MLP)) + abs(t["bout"][k]) for k in range(D_MODEL)]
    b["mlp_output"] = max(b_o)
    b_fin_pre = [b_r[k] * 256 + b_o[k] for k in range(D_MODEL)]
    b["final_stream"] = max(b_fin_pre)
    b_fin = [(v >> 16) + 1 for v in b_fin_pre]  # floor of a negative value can round away from zero
    b["unembed"] = max(sum(b_fin[k] * abs(t["U"][k][c]) for k in range(D_MODEL)) for c in range(P))
    return b


# ----------------------------------------------------------------------------------------------
# helpers


def fnv1a64(data, state):
    for byte in data:
        state = ((state ^ byte) * 0x100000001B3) & 0xFFFFFFFFFFFFFFFF
    return state


def sha256_path(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run_text(cmd, cwd):
    try:
        return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError) as e:
        return f"unavailable ({e.__class__.__name__})"


def rust_logits():
    """Every logit the Rust computes, from the dump_logits example. None if cargo cannot run."""
    try:
        done = subprocess.run(
            ["cargo", "run", "--release", "--locked", "--quiet", "--example", "dump_logits"],
            cwd=CRATE, capture_output=True, text=True,
        )
    except OSError as e:
        return None, f"cargo did not start: {e}"
    if done.returncode != 0:
        return None, f"cargo exited {done.returncode}: {done.stderr.strip()[-400:]}"
    table = {}
    for line in done.stdout.splitlines():
        parts = line.split()
        table[(int(parts[0]), int(parts[1]))] = [int(v) for v in parts[2:]]
    return table, "ok"


def parent_checks(parent, checkpoint, tables, model, all_logits, say):
    """Checks against lean-checked-network's own reference. Needs numpy."""
    try:
        import numpy as np
    except ImportError:
        say("parent cross-check: not run, numpy is not importable")
        return True
    sys.path.insert(0, str(Path(parent) / "transformer"))
    try:
        import int_transformer as it
    except ImportError as e:
        say(f"parent cross-check: not run, int_transformer.py not importable from {parent} ({e})")
        return True
    ok = True
    wq = it.quantise(it.load_weights(str(checkpoint)), gen.Q_BITS)
    names = ["tok", "pos", "WQ", "WK", "WV", "WO", "Win", "bin", "Wout", "bout", "U"]
    entries, differ = 0, 0
    for name in names:
        ours = np.array(tables[name], dtype=object).ravel()
        theirs = wq[name].ravel()
        entries += len(theirs)
        differ += sum(1 for x, y in zip(ours, theirs) if int(x) != int(y)) + abs(len(ours) - len(theirs))
    say(f"parent cross-check, quantised weights vs int_transformer.quantise(W, {gen.Q_BITS}): {entries} entries, {differ} differ")
    ok &= differ == 0
    tb = it.build_tables(wq)
    slots, bad = 0, 0
    for h in range(N_HEADS):
        for j in range(N_POS):
            for tok in (range(P) if j < 2 else [EQ]):
                slots += 1
                bad += int(tb["sc"][h][j][tok]) != model.score(h, tok, j)
    say(f"parent cross-check, attention scores vs int_transformer.build_tables sc: {slots} scores, {bad} differ")
    ok &= bad == 0
    pairs = np.array(sorted(all_logits))
    labels = (pairs[:, 0] + pairs[:, 1]) % P
    lq = it.float_logits(it.dequantise(wq), pairs, scale_scores=False)
    ours = np.array([[v / 2.0**32 for v in all_logits[tuple(p)]] for p in pairs.tolist()])
    dev = float(np.abs(ours - lq).max())
    mq = it.margins_of(lq, labels)
    say(f"parent cross-check, logits / 2^32 vs float64 forward of the quantised real-softmax model: max |difference| {dev:.6g} over {len(pairs)} pairs")
    say(f"parent cross-check, float64 quantised model: smallest margin {float(mq.min()):.6f}, wrong {int((lq.argmax(1) != labels).sum())}")
    return ok


# ----------------------------------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("checkpoint", type=Path)
    ap.add_argument("--parent", type=Path, default=None, help="a lean-checked-network checkout, for the cross-checks")
    ap.add_argument("--no-rust", action="store_true")
    ap.add_argument("--no-partials", action="store_true")
    ap.add_argument("--rows", type=int, default=P)
    args = ap.parse_args()
    full = args.rows == P

    lines = []

    def say(s=""):
        print(s, flush=True)
        lines.append(s)

    ok = True
    started = time.time()
    say(f"date: {time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}")
    say(f"python: {platform.python_version()}; rustc: {run_text(['rustc', '--version'], CRATE)}")
    say(f"run: rows {args.rows} of {P}; dot-product partial sums {'off' if args.no_partials else 'on'}; "
        f"rust comparison {'off' if args.no_rust else 'on'}; parent cross-check {'on' if args.parent else 'off'}")
    checkpoint_sha = gen.sha256_file(args.checkpoint)
    say(f"checkpoint: {args.checkpoint.name} sha256 {checkpoint_sha}")
    if checkpoint_sha != gen.CHECKPOINT_SHA256:
        say(f"FAIL: the pinned checkpoint sha256 is {gen.CHECKPOINT_SHA256}")
        ok = False
    tables = gen.load_quantised(args.checkpoint)
    generated = gen.render(tables, checkpoint_sha).encode("utf-8")
    on_disk = WEIGHTS_RS.read_bytes() if WEIGHTS_RS.exists() else b""
    same = generated == on_disk
    say(f"weights.rs: sha256 {hashlib.sha256(on_disk).hexdigest()}, {len(on_disk)} bytes, "
        f"{'identical to' if same else 'DIFFERENT from'} the generator's output")
    ok &= same
    say(f"lib.rs: sha256 {sha256_path(LIB_RS)}")
    for name in ("tok", "pos", "WQ", "WK", "WV", "WO", "Win", "bin", "Wout", "bout", "U"):
        flat = tables[name]
        while isinstance(flat[0], list):
            flat = [v for row in flat for v in row]
        say(f"weights {name}: {len(flat)} entries in [{min(flat)}, {max(flat)}]")

    table_ok = True
    for name in ("EXP_N", "EXP_2", "EXP_1", "EXP_0"):
        tab = tables[name]
        table_ok &= tab[0] == EXP_ONE and all(0 <= v <= EXP_ONE for v in tab)
        table_ok &= all(x >= y for x, y in zip(tab, tab[1:]))
    say(f"exp tables: {sum(len(tables[n]) for n in ('EXP_N', 'EXP_2', 'EXP_1', 'EXP_0'))} entries; "
        f"every entry in [0, 2^{EXP_FRAC_BITS}], entry 0 of each table 2^{EXP_FRAC_BITS}, no table increases: "
        f"{'yes' if table_ok else 'NO'}")
    ok &= table_ok
    cargo_toml = (CRATE / "Cargo.toml").read_text()
    profiles = {}
    section = None
    for raw in cargo_toml.splitlines():
        line = raw.strip()
        if line.startswith("["):
            section = line.strip("[]")
        elif line.replace(" ", "") == "overflow-checks=true" and section:
            profiles[section] = True
    checks_on = profiles.get("profile.dev", False) and profiles.get("profile.release", False)
    say(f"Cargo.toml: overflow-checks = true in profile.dev and profile.release: {'yes' if checks_on else 'NO'}")
    ok &= checks_on

    say()
    say("static bounds (from the weights alone; each covers every product and partial sum of its stage)")
    bounds = static_bounds(tables)
    for name, what, scale in STAGES:
        v = bounds[name]
        fits = v <= I64_MAX
        ok &= fits
        say(f"  {name:16s} <= {v:>22d}  {v.bit_length():2d} bits  {'fits i64' if fits else 'EXCEEDS i64'}")
    say(f"  largest static bound: {max(bounds.values()).bit_length()} bits; i64 holds 63")

    say()
    stats = Stats(partials=not args.no_partials)
    model = Model(tables, stats)
    all_logits = {}
    wrong, ties, min_margin, min_pair = 0, 0, None, None
    den_min, den_max = None, 0
    state = 0xCBF29CE484222325
    t0 = time.time()
    for a in range(args.rows):
        for b in range(P):
            out, dens = model.forward(a, b)
            all_logits[(a, b)] = out
            label = (a + b) % P
            if argmax_first(out) != label:
                wrong += 1
            margin = out[label] - max(out[c] for c in range(P) if c != label)
            if margin == 0:
                ties += 1
            if min_margin is None or margin < min_margin:
                min_margin, min_pair = margin, (a, b)
            den_min = min(dens) if den_min is None else min(den_min, min(dens))
            den_max = max(den_max, max(dens))
            state = fnv1a64(struct.pack(f"<{P}q", *out), state)
    secs = time.time() - t0
    pairs = len(all_logits)
    say(f"pairs evaluated: {pairs} ({args.rows} rows of {P}) in {secs:.0f} s")
    say(f"wrong: {wrong}; ties with the right answer: {ties}")
    say(f"smallest margin: {min_margin} at scale 2^32 ({min_margin / 2**32:.6f} logit units) at pair {min_pair}")
    say(f"softmax denominators: between {den_min} and {den_max} (2^30 = {EXP_ONE})")
    say(f"logits FNV-1a 64 (pair order a then b, each logit as 8 little-endian bytes): {state:016x}")
    ok &= wrong == 0 and min_margin > 0 and den_min >= EXP_ONE

    say()
    say("measured largest absolute values over the evaluated pairs")
    if not stats.partials:
        say("  (--no-partials: the products and partial sums inside the dot products were not measured)")
    say(f"  {'stage':16s} {'stage values':>22s} bits   {'products and partial sums':>26s} bits   scale  contents")
    for name, what, scale in STAGES:
        v, w = stats.out[name], stats.inner[name]
        say(f"  {name:16s} {v:>22d} {v.bit_length():4d}   {w:>26d} {w.bit_length():4d}   {scale:5s}  {what}")
        ok &= v <= I64_MAX and w <= I64_MAX
        if v > bounds[name] or w > bounds[name]:
            say(f"  FAIL: {name} exceeds its static bound")
            ok = False
    widest = max(max(stats.out.values()), max(stats.inner.values()))
    say(f"  widest measured value: {widest.bit_length()} bits; i64 holds 63")

    say()
    if full:
        FIXTURE.parent.mkdir(parents=True, exist_ok=True)
        FIXTURE.write_text(
            "# Written by scripts/check_transformer_int.py. Read by tests/all_pairs.rs.\n"
            f"logits_fnv1a64 {state:016x}\n"
            f"min_margin {min_margin}\n"
            f"min_margin_pair {min_pair[0]} {min_pair[1]}\n"
        )
        say(f"fixture: wrote {FIXTURE.relative_to(ROOT)}")
    else:
        say("fixture: not written (partial run)")

    if args.no_rust:
        say("rust comparison: not run (--no-rust)")
    else:
        table, status = rust_logits()
        if table is None:
            say(f"rust comparison: FAIL, {status}")
            ok = False
        else:
            compared = [p for p in all_logits if p in table]
            mismatched_logits = sum(
                sum(1 for x, y in zip(all_logits[p], table[p]) if x != y) + abs(len(all_logits[p]) - len(table[p]))
                for p in compared
            )
            missing = len(all_logits) - len(compared)
            say(f"rust comparison: {len(compared)} pairs, {len(compared) * P} logits compared, "
                f"{mismatched_logits} differ, {missing} pairs missing from the Rust output")
            ok &= mismatched_logits == 0 and missing == 0

    if args.parent is not None:
        ok &= parent_checks(args.parent, args.checkpoint, tables, model, all_logits, say)
    else:
        say("parent cross-check: not run (no --parent)")

    say()
    say(f"total time: {time.time() - started:.0f} s")
    say(f"result: {'PASS' if ok else 'FAIL'}")
    if full:
        SUMMARY.parent.mkdir(parents=True, exist_ok=True)
        SUMMARY.write_text("\n".join(lines) + "\n")
        print(f"wrote {SUMMARY.relative_to(ROOT)}")
    else:
        print("partial run: evidence not written")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
