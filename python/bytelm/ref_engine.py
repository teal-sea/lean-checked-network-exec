#!/usr/bin/env python3
"""Exact Python integer reference engine for the SPEC-E4-E6.md contract (`GLMW` v1).

Standard library only. This module is the bit-for-bit reference for the general
multi-layer causal integer language model of `docs/SPEC-E4-E6.md`:

- `pack` / `unpack`: the exact `GLMW` v1 binary weight format, 479,504 bytes.
- `load_check`: the range validation of the spec, on every coordinate.
- `Engine.forward_logits` / `Engine.predict_next` / `Engine.generate_greedy`:
  the exact integer forward semantics.

Arithmetic conventions (why this is bit-exact with the Rust):

- Rust `>>` on `i64` is the arithmetic shift, which floors toward minus infinity.
  Python `>>` on ints floors too, so every `>>` in the spec is written `>>` here.
- Rust signed `/` truncates toward zero (Lean `Int.tdiv`). The one division in
  the program, `alpha = e * 2^24 / denom`, has a nonnegative numerator and a
  positive denominator, so truncation and floor agree; `tdiv` below implements
  the truncating division explicitly anyway so the convention is stated in code.
- All intermediate values are exact Python integers (no wrapping). The caller
  can verify they fit `i64` with the static bound analysis in `eval_exact.py`.

Speed note: the reference computes, at the final active layer, only position
`seq_len - 1`. Earlier positions of the final layer have no consumer (there is
no inter-layer rescale out of the final layer and the unembed reads only
`p = seq_len - 1`), so their values cannot change any output. Non-final layers
compute every active position, as the spec requires. `forward_logits` returns
exactly the logits the full computation would return.

Layer-0 query/key/value projections are cached by `(head, position, token)`:
at layer 0 the stream row `x[p] = tok[tokens[p]] + pos[p]` depends on that pair
alone. This mirrors the caching of `scripts/check_transformer_int.py`.
"""

from __future__ import annotations

import struct
import sys
from array import array
from operator import mul

# ---------------------------------------------------------------- constants

MAX_LAYERS = 2
VOCAB = 256
MAX_SEQ = 32
D_MODEL = 128
N_HEADS = 4
D_HEAD = 32
D_MLP = 512

EXP_FRAC_BITS = 30
EXP_ONE = 1 << 30
EXP_N_LEN = 32
ALPHA_ONE = 1 << 24

I64_MIN = -(1 << 63)
I64_MAX = (1 << 63) - 1

MAGIC = b"GLMW"
VERSION = 1
FILE_SIZE = 479504  # exact size of a GLMW v1 file

# load_check boxes from SPEC-E4-E6.md section 3.
TOK_BOX = 68
POS_BOX = 59
WQ_BOX = 5
WK_BOX = 22
WV_BOX = 106
WO_BOX = 93
WIN_BOX = 82
WOUT_BOX = 74
U_BOX = 37
BIN_BOX = 1 << 30
BOUT_BOX = 1 << 37


def tdiv(a: int, b: int) -> int:
    """Rust `i64` division: truncate toward zero (Lean `Int.tdiv`).

    Python `//` floors; for the operands of this program (numerator >= 0,
    denominator > 0) the two agree, but the convention is written out here.
    """
    if b == 0:
        raise ZeroDivisionError("tdiv by zero")
    q = abs(a) // abs(b)
    return q if (a < 0) == (b < 0) else -q


def _zeros(*shape: int) -> list:
    """A nested zero list of the given shape."""
    if len(shape) == 1:
        return [0] * shape[0]
    return [_zeros(*shape[1:]) for _ in range(shape[0])]


# ---------------------------------------------------------------- weights


class LayerWeights:
    """One transformer layer, exactly the struct of SPEC-E4-E6.md section 2."""

    __slots__ = ("wq", "wk", "wv", "wo", "win", "bin", "wout", "bout")

    def __init__(self, wq=None, wk=None, wv=None, wo=None, win=None, bin_=None,
                 wout=None, bout=None):
        self.wq = wq if wq is not None else _zeros(N_HEADS, D_MODEL, D_HEAD)
        self.wk = wk if wk is not None else _zeros(N_HEADS, D_MODEL, D_HEAD)
        self.wv = wv if wv is not None else _zeros(N_HEADS, D_MODEL, D_HEAD)
        self.wo = wo if wo is not None else _zeros(N_HEADS, D_HEAD, D_MODEL)
        self.win = win if win is not None else _zeros(D_MODEL, D_MLP)
        self.bin = bin_ if bin_ is not None else _zeros(D_MLP)
        self.wout = wout if wout is not None else _zeros(D_MLP, D_MODEL)
        self.bout = bout if bout is not None else _zeros(D_MODEL)


class Weights:
    """The whole model, exactly the struct of SPEC-E4-E6.md section 2."""

    __slots__ = ("n_layers", "vocab_size", "tok", "pos", "layers", "u",
                 "exp_n", "exp_2", "exp_1", "exp_0", "_engine")

    def __init__(self, n_layers: int, vocab_size: int, tok=None, pos=None,
                 layers=None, u=None, exp_n=None, exp_2=None, exp_1=None,
                 exp_0=None):
        self.n_layers = n_layers
        self.vocab_size = vocab_size
        self.tok = tok if tok is not None else _zeros(VOCAB, D_MODEL)
        self.pos = pos if pos is not None else _zeros(MAX_SEQ, D_MODEL)
        self.layers = layers if layers is not None else [LayerWeights() for _ in range(MAX_LAYERS)]
        self.u = u if u is not None else _zeros(D_MODEL, VOCAB)
        self.exp_n = exp_n if exp_n is not None else _zeros(EXP_N_LEN)
        self.exp_2 = exp_2 if exp_2 is not None else _zeros(256)
        self.exp_1 = exp_1 if exp_1 is not None else _zeros(256)
        self.exp_0 = exp_0 if exp_0 is not None else _zeros(256)
        self._engine = None


# ---------------------------------------------------------------- GLMW v1 pack / unpack


def _flatten(nested: list) -> list:
    out = []
    stack = [nested]
    while stack:
        item = stack.pop()
        if isinstance(item, list):
            stack.extend(reversed(item))
        else:
            out.append(item)
    return out


def _nest(flat: list, shape) -> list:
    if len(shape) == 1:
        if len(flat) != shape[0]:
            raise ValueError("shape mismatch")
        return list(flat)
    step = len(flat) // shape[0]
    return [_nest(flat[i * step:(i + 1) * step], shape[1:]) for i in range(shape[0])]


def pack(w: Weights) -> bytes:
    """Serialize to the exact GLMW v1 byte layout (479,504 bytes).

    Raises ValueError if a value does not fit its integer type.
    """
    parts = [struct.pack("<4sIII", MAGIC, VERSION, w.n_layers, w.vocab_size)]

    def i8_block(nested, shape, name):
        flat = _flatten(nested)
        if len(flat) != _prod(shape):
            raise ValueError(f"{name}: {len(flat)} values, shape {shape}")
        try:
            return array("b", flat).tobytes()
        except OverflowError:
            lo, hi = min(flat), max(flat)
            raise ValueError(f"{name}: entries in [{lo}, {hi}] do not fit i8") from None

    def i64_block(flat, name):
        try:
            return struct.pack(f"<{len(flat)}q", *flat)
        except struct.error:
            lo, hi = min(flat), max(flat)
            raise ValueError(f"{name}: entries in [{lo}, {hi}] do not fit i64") from None

    parts.append(i8_block(w.tok, (VOCAB, D_MODEL), "tok"))
    parts.append(i8_block(w.pos, (MAX_SEQ, D_MODEL), "pos"))
    for lw in w.layers:
        parts.append(i8_block(lw.wq, (N_HEADS, D_MODEL, D_HEAD), "wq"))
        parts.append(i8_block(lw.wk, (N_HEADS, D_MODEL, D_HEAD), "wk"))
        parts.append(i8_block(lw.wv, (N_HEADS, D_MODEL, D_HEAD), "wv"))
        parts.append(i8_block(lw.wo, (N_HEADS, D_HEAD, D_MODEL), "wo"))
        parts.append(i8_block(lw.win, (D_MODEL, D_MLP), "win"))
        parts.append(i64_block(list(lw.bin), "bin"))
        parts.append(i8_block(lw.wout, (D_MLP, D_MODEL), "wout"))
        parts.append(i64_block(list(lw.bout), "bout"))
    parts.append(i8_block(w.u, (D_MODEL, VOCAB), "u"))
    parts.append(i64_block(list(w.exp_n), "exp_n"))
    parts.append(i64_block(list(w.exp_2), "exp_2"))
    parts.append(i64_block(list(w.exp_1), "exp_1"))
    parts.append(i64_block(list(w.exp_0), "exp_0"))
    data = b"".join(parts)
    if len(data) != FILE_SIZE:
        raise ValueError(f"packed {len(data)} bytes, the GLMW v1 layout is {FILE_SIZE}")
    return data


def _prod(shape) -> int:
    n = 1
    for s in shape:
        n *= s
    return n


def unpack(data: bytes) -> Weights:
    """Parse a GLMW v1 file into a Weights object. Raises ValueError if malformed."""
    if len(data) != FILE_SIZE:
        raise ValueError(f"{len(data)} bytes, a GLMW v1 file is exactly {FILE_SIZE}")
    magic, version, n_layers, vocab_size = struct.unpack_from("<4sIII", data, 0)
    if magic != MAGIC:
        raise ValueError(f"magic {magic!r}, expected {MAGIC!r}")
    if version != VERSION:
        raise ValueError(f"version {version}, expected {VERSION}")
    off = 16

    def take_i8(count):
        nonlocal off
        vals = array("b", data[off:off + count]).tolist()
        off += count
        return vals

    def take_i64(count):
        nonlocal off
        vals = list(struct.unpack_from(f"<{count}q", data, off))
        off += count * 8
        return vals

    tok = _nest(take_i8(VOCAB * D_MODEL), (VOCAB, D_MODEL))
    pos = _nest(take_i8(MAX_SEQ * D_MODEL), (MAX_SEQ, D_MODEL))
    layers = []
    for _ in range(MAX_LAYERS):
        wq = _nest(take_i8(N_HEADS * D_MODEL * D_HEAD), (N_HEADS, D_MODEL, D_HEAD))
        wk = _nest(take_i8(N_HEADS * D_MODEL * D_HEAD), (N_HEADS, D_MODEL, D_HEAD))
        wv = _nest(take_i8(N_HEADS * D_MODEL * D_HEAD), (N_HEADS, D_MODEL, D_HEAD))
        wo = _nest(take_i8(N_HEADS * D_HEAD * D_MODEL), (N_HEADS, D_HEAD, D_MODEL))
        win = _nest(take_i8(D_MODEL * D_MLP), (D_MODEL, D_MLP))
        bin_ = take_i64(D_MLP)
        wout = _nest(take_i8(D_MLP * D_MODEL), (D_MLP, D_MODEL))
        bout = take_i64(D_MODEL)
        layers.append(LayerWeights(wq, wk, wv, wo, win, bin_, wout, bout))
    u = _nest(take_i8(D_MODEL * VOCAB), (D_MODEL, VOCAB))
    exp_n = take_i64(EXP_N_LEN)
    exp_2 = take_i64(256)
    exp_1 = take_i64(256)
    exp_0 = take_i64(256)
    if off != FILE_SIZE:
        raise ValueError(f"parsed to offset {off}, expected {FILE_SIZE}")
    return Weights(n_layers, vocab_size, tok, pos, layers, u, exp_n, exp_2, exp_1, exp_0)


def load(path) -> Weights:
    with open(path, "rb") as f:
        return unpack(f.read())


def save(w: Weights, path) -> None:
    with open(path, "wb") as f:
        f.write(pack(w))


# ---------------------------------------------------------------- load_check


def load_check(w: Weights) -> bool:
    """Every range condition of SPEC-E4-E6.md section 3."""
    if w.n_layers < 1 or w.n_layers > MAX_LAYERS:
        return False
    if w.vocab_size < 1 or w.vocab_size > VOCAB:
        return False
    for t in range(VOCAB):
        row = w.tok[t]
        for k in range(D_MODEL):
            if row[k] < -TOK_BOX or row[k] > TOK_BOX:
                return False
    for p in range(MAX_SEQ):
        row = w.pos[p]
        for k in range(D_MODEL):
            if row[k] < -POS_BOX or row[k] > POS_BOX:
                return False
    for lw in w.layers:
        for h in range(N_HEADS):
            for i in range(D_MODEL):
                row = lw.wq[h][i]
                for j in range(D_HEAD):
                    if row[j] < -WQ_BOX or row[j] > WQ_BOX:
                        return False
                row = lw.wk[h][i]
                for j in range(D_HEAD):
                    if row[j] < -WK_BOX or row[j] > WK_BOX:
                        return False
                row = lw.wv[h][i]
                for j in range(D_HEAD):
                    if row[j] < -WV_BOX or row[j] > WV_BOX:
                        return False
            for j in range(D_HEAD):
                row = lw.wo[h][j]
                for i in range(D_MODEL):
                    if row[i] < -WO_BOX or row[i] > WO_BOX:
                        return False
            for i in range(D_MODEL):
                row = lw.win[i]
                for m in range(D_MLP):
                    if row[m] < -WIN_BOX or row[m] > WIN_BOX:
                        return False
        for m in range(D_MLP):
            if lw.bin[m] < -BIN_BOX or lw.bin[m] > BIN_BOX:
                return False
        for i in range(D_MLP):
            row = lw.wout[i]
            for k in range(D_MODEL):
                if row[k] < -WOUT_BOX or row[k] > WOUT_BOX:
                    return False
        for k in range(D_MODEL):
            if lw.bout[k] < -BOUT_BOX or lw.bout[k] > BOUT_BOX:
                return False
    for i in range(D_MODEL):
        row = w.u[i]
        for v in range(VOCAB):
            if row[v] < -U_BOX or row[v] > U_BOX:
                return False
    for table in (w.exp_n, w.exp_2, w.exp_1, w.exp_0):
        for v in table:
            if v < 0 or v > EXP_ONE:
                return False
    return True


# ---------------------------------------------------------------- engine


class Engine:
    """The exact forward program of SPEC-E4-E6.md section 4, on Python ints."""

    def __init__(self, w: Weights):
        self.w = w
        self.vocab = w.vocab_size
        # Column-major views, so each dot product reads one contiguous list.
        self.wq_cols = []
        self.wk_cols = []
        self.wv_cols = []
        self.wo_cols = []
        self.win_cols = []
        self.wout_cols = []
        for lw in w.layers:
            self.wq_cols.append(
                [[[lw.wq[h][k][i] for k in range(D_MODEL)] for i in range(D_HEAD)]
                 for h in range(N_HEADS)])
            self.wk_cols.append(
                [[[lw.wk[h][k][i] for k in range(D_MODEL)] for i in range(D_HEAD)]
                 for h in range(N_HEADS)])
            self.wv_cols.append(
                [[[lw.wv[h][k][i] for k in range(D_MODEL)] for i in range(D_HEAD)]
                 for h in range(N_HEADS)])
            self.wo_cols.append(
                [[[lw.wo[h][t][k] for t in range(D_HEAD)] for k in range(D_MODEL)]
                 for h in range(N_HEADS)])
            self.win_cols.append(
                [[lw.win[k][i] for k in range(D_MODEL)] for i in range(D_MLP)])
            self.wout_cols.append(
                [[lw.wout[i][k] for i in range(D_MLP)] for k in range(D_MODEL)])
        self.u_cols = [[w.u[k][v] for k in range(D_MODEL)] for v in range(self.vocab)]
        self.exp_n = w.exp_n
        self.exp_2 = w.exp_2
        self.exp_1 = w.exp_1
        self.exp_0 = w.exp_0
        # Layer-0 caches: x[p] at layer 0 depends only on (p, tokens[p]).
        self._x0 = {}
        self._proj0 = {}

    # -- small pieces -----------------------------------------------------

    def _embed0(self, p: int, tok: int) -> list:
        key = (p, tok)
        got = self._x0.get(key)
        if got is None:
            w = self.w
            got = [w.tok[tok][k] + w.pos[p][k] for k in range(D_MODEL)]
            self._x0[key] = got
        return got

    def _project0(self, which: str, h: int, p: int, tok: int) -> list:
        key = (which, h, p, tok)
        got = self._proj0.get(key)
        if got is None:
            x = self._embed0(p, tok)
            cols = {"q": self.wq_cols, "k": self.wk_cols, "v": self.wv_cols}[which][0][h]
            got = [sum(map(mul, x, col)) for col in cols]
            self._proj0[key] = got
        return got

    def _qkv(self, l: int, which: str, h: int, p: int, x, tokens) -> list:
        if l == 0:
            return self._project0(which, h, p, tokens[p])
        cols = {"q": self.wq_cols, "k": self.wk_cols, "v": self.wv_cols}[which][l][h]
        return [sum(map(mul, x[p], col)) for col in cols]

    def exp_fix(self, d: int) -> int:
        """The table exp of SPEC-E4-E6.md: round(2^30 exp(-d / 2^32)) for d >= 0."""
        if d <= 0:
            return EXP_ONE
        u = d >> 8
        n = u >> 24
        if n >= EXP_N_LEN:
            return 0
        e = self.exp_n[n]
        e = (e * self.exp_2[(u >> 16) & 255]) >> EXP_FRAC_BITS
        e = (e * self.exp_1[(u >> 8) & 255]) >> EXP_FRAC_BITS
        e = (e * self.exp_0[u & 255]) >> EXP_FRAC_BITS
        return e

    # -- forward ----------------------------------------------------------

    def forward_logits(self, tokens, seq_len: int | None = None):
        """`logits[v]` for `v` in `0..vocab_size`, or None if the guard rejects.

        `tokens` holds at least `seq_len` token ids in `0..255`.
        """
        tokens = list(tokens)
        if seq_len is None:
            seq_len = len(tokens)
        w = self.w
        if seq_len == 0 or seq_len > MAX_SEQ:
            return None
        if w.n_layers == 0 or w.n_layers > MAX_LAYERS or w.vocab_size == 0 or w.vocab_size > VOCAB:
            return None
        for p in range(seq_len):
            if tokens[p] >= VOCAB:
                return None

        x = [self._embed0(p, tokens[p]) for p in range(seq_len)]
        last_hidden = None
        for l in range(w.n_layers):
            final = (l + 1 == w.n_layers)
            positions = (range(seq_len - 1, seq_len) if final else range(seq_len))
            if final:
                for p in positions:
                    att = self._attend(l, x, p, tokens)
                    r, f = self._mlp(l, x[p], att)
                    last_hidden = f
            else:
                nxt = [[0] * D_MODEL for _ in range(seq_len)]
                for p in positions:
                    att = self._attend(l, x, p, tokens)
                    r, f = self._mlp(l, x[p], att)
                    row = nxt[p]
                    for k in range(D_MODEL):
                        s = f[k] >> 16
                        row[k] = -127 if s < -127 else (127 if s > 127 else s)
                x = nxt
        return [sum(map(mul, last_hidden, col)) for col in self.u_cols]

    def _attend(self, l: int, x, p: int, tokens) -> list:
        """Causal attention output at (layer, position), scale 2^32, over j <= p."""
        att = [0] * D_MODEL
        wo_cols = self.wo_cols[l]
        for h in range(N_HEADS):
            q = self._qkv(l, "q", h, p, x, tokens)
            scores = []
            for j in range(p + 1):
                key = self._qkv(l, "k", h, j, x, tokens)
                scores.append(sum(map(mul, q, key)))
            smax = scores[0]
            for j in range(1, p + 1):
                if scores[j] > smax:
                    smax = scores[j]
            e = [self.exp_fix(smax - s) for s in scores]
            den = 0
            for v in e:
                den += v
            alpha = [tdiv(v * ALPHA_ONE, den) for v in e]
            vs = [self._qkv(l, "v", h, j, x, tokens) for j in range(p + 1)]
            np1 = p + 1
            z = []
            for i in range(D_HEAD):
                acc = 0
                for j in range(np1):
                    acc += alpha[j] * vs[j][i]
                z.append(acc >> 16)
            cols = wo_cols[h]
            for k in range(D_MODEL):
                att[k] += sum(map(mul, z, cols[k]))
        return att

    def _mlp(self, l: int, xrow, att) -> tuple:
        """Residual, MLP and final stream at one position.

        Returns `(r, f)`: the residual at scale 2^32 and the final stream at
        scale 2^24.
        """
        win_cols = self.win_cols[l]
        wout_cols = self.wout_cols[l]
        lw = self.w.layers[l]
        r = [xrow[k] * ALPHA_ONE + att[k] for k in range(D_MODEL)]
        bin_ = lw.bin
        m = []
        for i in range(D_MLP):
            pre = sum(map(mul, r, win_cols[i])) + bin_[i] * 256
            m.append(pre >> 8 if pre > 0 else 0)
        bout = lw.bout
        f = []
        for k in range(D_MODEL):
            o = sum(map(mul, m, wout_cols[k])) + bout[k]
            f.append((r[k] * 256 + o) >> 16)
        return r, f

    # -- API on top of forward --------------------------------------------

    def predict_next(self, tokens, seq_len: int | None = None):
        """Strict-`>` first argmax over `0..vocab_size`, or None if rejected."""
        logits = self.forward_logits(tokens, seq_len)
        if logits is None:
            return None
        best, best_value = 0, logits[0]
        for c in range(1, len(logits)):
            if logits[c] > best_value:
                best_value, best = logits[c], c
        return best

    def generate_greedy(self, prompt, steps: int = MAX_SEQ):
        """Greedy generation from `prompt`, appending up to `steps` tokens.

        The buffer never exceeds `MAX_SEQ` tokens: a prompt longer than
        `MAX_SEQ` keeps its last `MAX_SEQ` bytes. Returns the full token list
        (prompt plus generated); its length is the final length of the spec's
        `buf`, and None if the first forward is rejected.
        """
        buf = list(prompt)[-(MAX_SEQ):]
        cur = len(buf)
        if cur == 0:
            return None
        first = self.predict_next(buf, cur)
        if first is None:
            return None
        for _ in range(steps):
            if cur >= MAX_SEQ:
                break
            nxt = self.predict_next(buf, cur)
            if nxt is None:
                break
            buf.append(nxt)
            cur += 1
        return buf


# ---------------------------------------------------------------- module-level API


def _engine_for(w: Weights) -> Engine:
    if w._engine is None:
        w._engine = Engine(w)
    return w._engine


def forward_logits(w: Weights, tokens, seq_len: int | None = None):
    return _engine_for(w).forward_logits(tokens, seq_len)


def predict_next(w: Weights, tokens, seq_len: int | None = None):
    return _engine_for(w).predict_next(tokens, seq_len)


def generate_greedy(w: Weights, prompt, steps: int = MAX_SEQ):
    return _engine_for(w).generate_greedy(prompt, steps)


# ---------------------------------------------------------------- self-test


def _self_test() -> int:
    import random

    rng = random.Random(20261120)

    def box(shape, lo, hi):
        return _nest([rng.randint(lo, hi) for _ in range(_prod(shape))], shape)

    exp_n = [EXP_ONE] + [0] * 31
    exp_2 = [EXP_ONE] * 256
    exp_1 = [EXP_ONE] * 256
    exp_0 = [EXP_ONE] * 256
    layers = []
    for _ in range(2):
        layers.append(LayerWeights(
            box((N_HEADS, D_MODEL, D_HEAD), -WQ_BOX, WQ_BOX),
            box((N_HEADS, D_MODEL, D_HEAD), -WK_BOX, WK_BOX),
            box((N_HEADS, D_MODEL, D_HEAD), -WV_BOX, WV_BOX),
            box((N_HEADS, D_HEAD, D_MODEL), -WO_BOX, WO_BOX),
            box((D_MODEL, D_MLP), -WIN_BOX, WIN_BOX),
            [rng.randint(-BIN_BOX, BIN_BOX) for _ in range(D_MLP)],
            box((D_MLP, D_MODEL), -WOUT_BOX, WOUT_BOX),
            [rng.randint(-BOUT_BOX, BOUT_BOX) for _ in range(D_MODEL)],
        ))
    w = Weights(
        2, 256,
        box((VOCAB, D_MODEL), -TOK_BOX, TOK_BOX),
        box((MAX_SEQ, D_MODEL), -POS_BOX, POS_BOX),
        layers,
        box((D_MODEL, VOCAB), -U_BOX, U_BOX),
        exp_n, exp_2, exp_1, exp_0,
    )
    assert load_check(w), "random in-box weights must pass load_check"
    data = pack(w)
    assert len(data) == FILE_SIZE, len(data)
    w2 = unpack(data)
    assert load_check(w2)
    assert w2.tok == w.tok and w2.layers[1].bout == w.layers[1].bout and w2.u == w.u
    e = Engine(w2)
    logits = e.forward_logits([7, 42, 100], 3)
    assert logits is not None and len(logits) == 256
    assert all(I64_MIN <= v <= I64_MAX for v in logits), "logits must fit i64"
    assert e.forward_logits([1, 2], 0) is None, "seq_len 0 is rejected"
    assert e.forward_logits([256], 1) is None, "token >= 256 is rejected"
    zl = e.predict_next([5, 9, 3], 3)
    assert isinstance(zl, int)
    buf = e.generate_greedy([1, 2, 3], 5)
    assert buf is not None and 4 <= len(buf) <= MAX_SEQ
    print("ref_engine self-test: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(_self_test())
