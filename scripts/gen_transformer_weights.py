#!/usr/bin/env python3
"""Generate rust/transformer/src/weights.rs from the trained transformer checkpoint.

Standard library only. The same checkpoint gives the same bytes on every machine.

Input: lean-checked-network's transformer/runs/best.npz, the float64 checkpoint behind
TransformerBridge.FinalRaw.raw_model_adds_mod_113. Its sha256 is pinned below, the value that
repository keeps in transformer/mathlib/RawPilot-pins.json.

Quantisation: the rule of lean-checked-network's transformer/int_transformer.py quantise(W, 8),
with S = 256 and rounding floor(v + 1/2) on float64 values:

    tok, pos, WK, WV, WO, Win, Wout, U   round(S * w)
    WQ                                   round(S * w / sqrt(32))   the 1/sqrt(32) of the score
    bin                                  round(S^4 * b)
    bout                                 round(S^5 * b)

The nine matrices fit i8 at S = 256 and are emitted as i8. The script fails if one entry does
not fit. The two bias vectors are emitted as i64.

Exponential tables for the integer softmax, each entry round(2^30 * exp(-y)) with rounding half
up, computed in exact rational arithmetic from a bracket of exp(-y) whose two ends round to the
same integer:

    EXP_N[n]   y = n            n = 0..31
    EXP_2[b]   y = b / 2^8      b = 0..255
    EXP_1[b]   y = b / 2^16     b = 0..255
    EXP_0[b]   y = b / 2^24     b = 0..255

Usage:
  gen_transformer_weights.py CHECKPOINT.npz            write rust/transformer/src/weights.rs
  gen_transformer_weights.py CHECKPOINT.npz --check    compare with the file on disk, exit 1 if it differs
  gen_transformer_weights.py CHECKPOINT.npz --out PATH write somewhere else
  --allow-other-checkpoint                             skip the sha256 pin (for experiments only)
"""

import argparse
import ast
import hashlib
import math
import struct
import sys
import zipfile
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_OUT = ROOT / "rust" / "transformer" / "src" / "weights.rs"

# transformer/runs/best.npz at lean-checked-network 0214aa3 (transformer/mathlib/RawPilot-pins.json).
CHECKPOINT_SHA256 = "7cea95ed6771691dfe8a29bedfdae72d9a62c8947c25b1bca2c56919c0ff0f9e"

P = 113
VOCAB = 114
D_MODEL, N_HEADS, D_HEAD, D_MLP = 128, 4, 32, 512
Q_BITS = 8
S = 1 << Q_BITS

EXP_FRAC_BITS = 30
EXP_N_LEN = 32

# name in the checkpoint -> (expected shape, Rust name)
MATRICES = {
    "tok": ((VOCAB, D_MODEL), "TOK"),
    "pos": ((3, D_MODEL), "POS"),
    "WQ": ((N_HEADS, D_MODEL, D_HEAD), "WQ"),
    "WK": ((N_HEADS, D_MODEL, D_HEAD), "WK"),
    "WV": ((N_HEADS, D_MODEL, D_HEAD), "WV"),
    "WO": ((N_HEADS, D_HEAD, D_MODEL), "WO"),
    "Win": ((D_MODEL, D_MLP), "WIN"),
    "Wout": ((D_MLP, D_MODEL), "WOUT"),
    "U": ((D_MODEL, P), "U"),
}
BIASES = {
    "bin": ((D_MLP,), "BIN"),
    "bout": ((D_MODEL,), "BOUT"),
}


def sha256_file(path):
    with open(path, "rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


def read_npy(raw):
    """Shape and flat values of a little-endian float64, C-order .npy file."""
    if raw[:6] != b"\x93NUMPY":
        raise ValueError("not an .npy file")
    major = raw[6]
    if major == 1:
        (hlen,) = struct.unpack("<H", raw[8:10])
        start = 10
    elif major in (2, 3):
        (hlen,) = struct.unpack("<I", raw[8:12])
        start = 12
    else:
        raise ValueError(f"unknown .npy version {major}")
    header = ast.literal_eval(raw[start : start + hlen].decode("latin1"))
    if header["descr"] != "<f8" or header["fortran_order"]:
        raise ValueError(f"expected little-endian float64 in C order, got {header}")
    shape = tuple(header["shape"])
    count = math.prod(shape)
    data = raw[start + hlen :]
    if len(data) != 8 * count:
        raise ValueError(f"expected {8 * count} data bytes, got {len(data)}")
    return shape, struct.unpack(f"<{count}d", data)


def load_checkpoint(path):
    """The eleven float64 arrays of the checkpoint as (shape, flat tuple)."""
    arrays = {}
    with zipfile.ZipFile(path) as z:
        for name, (shape, _) in {**MATRICES, **BIASES}.items():
            got_shape, values = read_npy(z.read(name + ".npy"))
            if got_shape != shape:
                raise ValueError(f"{name}: expected shape {shape}, got {got_shape}")
            arrays[name] = (shape, values)
    return arrays


def rnd(v):
    """Round half up, floor(v + 1/2), as int_transformer.py rnd."""
    return int(math.floor(v + 0.5))


def quantise(arrays):
    """Flat integer lists at S = 256, by the rule in the module docstring."""
    sqrt_d_head = math.sqrt(D_HEAD)
    scale = float(S)
    out = {}
    for name in ("tok", "pos", "WK", "WV", "WO", "Win", "Wout", "U"):
        out[name] = [rnd(scale * w) for w in arrays[name][1]]
    out["WQ"] = [rnd(scale * w / sqrt_d_head) for w in arrays["WQ"][1]]
    out["bin"] = [rnd(float(S**4) * b) for b in arrays["bin"][1]]
    out["bout"] = [rnd(float(S**5) * b) for b in arrays["bout"][1]]
    for name in MATRICES:
        lo, hi = min(out[name]), max(out[name])
        if lo < -128 or hi > 127:
            raise ValueError(f"{name}: entries in [{lo}, {hi}] do not fit i8")
    return out


def nest(flat, shape):
    """A flat list as nested lists of the given shape."""
    if len(shape) == 1:
        if len(flat) != shape[0]:
            raise ValueError("shape mismatch")
        return list(flat)
    step = len(flat) // shape[0]
    return [nest(flat[i * step : (i + 1) * step], shape[1:]) for i in range(shape[0])]


def load_quantised(path):
    """The integer model: nested lists keyed by checkpoint name, plus the four exp tables."""
    flat = quantise(load_checkpoint(path))
    model = {name: nest(flat[name], shape) for name, (shape, _) in {**MATRICES, **BIASES}.items()}
    model.update(exp_tables())
    return model


# ----------------------------------------------------------------------------------------------
# exp tables, exact


def _round_half_up(x):
    return math.floor(x + Fraction(1, 2))


def _exp_neg_bracket(y, terms):
    """Rational lower and upper bounds for exp(-y), 0 <= y <= 1.

    The series sum (-y)^i / i! alternates with terms that do not grow, so the value lies between
    any two consecutive partial sums.
    """
    if not 0 <= y <= 1:
        raise ValueError("bracket needs 0 <= y <= 1")
    partial, term = Fraction(0), Fraction(1)
    sums = []
    for i in range(terms + 1):
        partial += term
        sums.append(partial)
        term = term * (-y) / (i + 1)
    a, b = sums[-2], sums[-1]
    return min(a, b), max(a, b)


def _table_entry(bracket):
    lo, hi = bracket
    a = _round_half_up(lo * (1 << EXP_FRAC_BITS))
    b = _round_half_up(hi * (1 << EXP_FRAC_BITS))
    if a != b:
        raise ValueError("exp bracket straddles a rounding boundary: raise the number of terms")
    return a


def exp_tables():
    lo1, hi1 = _exp_neg_bracket(Fraction(1), 60)
    exp_n = [_table_entry((lo1**n, hi1**n)) for n in range(EXP_N_LEN)]
    tables = {"EXP_N": exp_n}
    for name, shift in (("EXP_2", 8), ("EXP_1", 16), ("EXP_0", 24)):
        tables[name] = [_table_entry(_exp_neg_bracket(Fraction(b, 1 << shift), 24)) for b in range(256)]
    for name in ("EXP_N", "EXP_2", "EXP_1", "EXP_0"):
        if tables[name][0] != 1 << EXP_FRAC_BITS:
            raise ValueError(f"{name}[0] must be 2^{EXP_FRAC_BITS}")
    return tables


# ----------------------------------------------------------------------------------------------
# Rust emission


def _rows(values, indent, width=100):
    """Comma-separated integers wrapped to `width` columns."""
    lines, line = [], indent
    for v in values:
        piece = f"{v}, "
        if len(line) + len(piece) > width + 1 and line.strip():
            lines.append(line.rstrip())
            line = indent
        line += piece
    if line.strip():
        lines.append(line.rstrip())
    return lines


def _emit_array(nested, depth):
    indent = "    " * depth
    if not isinstance(nested[0], list):
        return [indent + "["] + _rows(nested, indent + "    ") + [indent + "],"]
    lines = [indent + "["]
    for sub in nested:
        lines += _emit_array(sub, depth + 1)
    lines.append(indent + "],")
    return lines


def _rust_type(shape, elem):
    t = elem
    for n in reversed(shape):
        t = f"[{t}; {n}]"
    return t


def _emit_static(name, nested, shape, elem, doc):
    lines = [f"/// {d}" for d in doc]
    lines.append(f"pub static {name}: {_rust_type(shape, elem)} = [")
    body = _emit_array(nested, 0)[1:]
    body[-1] = "];"
    return lines + body + [""]


def render(model, checkpoint_sha256):
    lines = [
        "// @generated by scripts/gen_transformer_weights.py. Do not edit.",
        "//",
        "// Checkpoint: lean-checked-network transformer/runs/best.npz",
        f"// Checkpoint sha256: {checkpoint_sha256}",
        f"// Quantisation: int_transformer.py quantise(W, {Q_BITS}); S = {S}; round half up on float64.",
        "//   tok, pos, WK, WV, WO, Win, Wout, U: round(S * w).  WQ: round(S * w / sqrt(32)).",
        "//   bin: round(S^4 * b).  bout: round(S^5 * b).",
        f"// Exp tables: round(2^{EXP_FRAC_BITS} * exp(-y)), round half up, exact rational brackets.",
        "",
        "/// Fractional bits of the exponential tables.",
        f"pub const EXP_FRAC_BITS: u32 = {EXP_FRAC_BITS};",
        f"/// 2^{EXP_FRAC_BITS}, the table value of exp(0).",
        f"pub const EXP_ONE: i64 = {1 << EXP_FRAC_BITS};",
        "",
    ]
    docs = {
        "tok": ["Token embedding, scale 2^8. Row = token (0..112, and 113 for `=`), column = stream index."],
        "pos": ["Position embedding, scale 2^8. Row = position, column = stream index."],
        "WQ": ["Query matrices, scale 2^8, with 1/sqrt(32) folded in. `WQ[h][k][i]`: head, stream index, head index."],
        "WK": ["Key matrices, scale 2^8. `WK[h][k][i]`: head, stream index, head index."],
        "WV": ["Value matrices, scale 2^8. `WV[h][k][i]`: head, stream index, head index."],
        "WO": ["Output matrices, scale 2^8. `WO[h][i][k]`: head, head index, stream index."],
        "Win": ["MLP input matrix, scale 2^8. `WIN[k][i]`: stream index, hidden index."],
        "bin": ["MLP input bias, scale 2^32."],
        "Wout": ["MLP output matrix, scale 2^8. `WOUT[i][k]`: hidden index, stream index."],
        "bout": ["MLP output bias, scale 2^40."],
        "U": ["Unembedding, scale 2^8. `U[k][c]`: stream index, answer."],
    }
    for name in ("tok", "pos", "WQ", "WK", "WV", "WO", "Win", "bin", "Wout", "bout", "U"):
        if name in MATRICES:
            shape, rust = MATRICES[name]
            elem = "i8"
        else:
            shape, rust = BIASES[name]
            elem = "i64"
        lines += _emit_static(rust, model[name], shape, elem, docs[name])
    exp_docs = {
        "EXP_N": "`EXP_N[n]` = round(2^30 * exp(-n)).",
        "EXP_2": "`EXP_2[b]` = round(2^30 * exp(-b / 2^8)).",
        "EXP_1": "`EXP_1[b]` = round(2^30 * exp(-b / 2^16)).",
        "EXP_0": "`EXP_0[b]` = round(2^30 * exp(-b / 2^24)).",
    }
    for name in ("EXP_N", "EXP_2", "EXP_1", "EXP_0"):
        lines += _emit_static(name, model[name], (len(model[name]),), "i64", [exp_docs[name]])
    while lines and lines[-1] == "":
        lines.pop()
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("checkpoint", type=Path)
    ap.add_argument("--out", type=Path, default=DEFAULT_OUT)
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--allow-other-checkpoint", action="store_true")
    args = ap.parse_args()

    checkpoint_sha = sha256_file(args.checkpoint)
    if checkpoint_sha != CHECKPOINT_SHA256 and not args.allow_other_checkpoint:
        print(f"FAIL: checkpoint sha256 {checkpoint_sha}, pinned {CHECKPOINT_SHA256}", file=sys.stderr)
        return 1
    text = render(load_quantised(args.checkpoint), checkpoint_sha)
    data = text.encode("utf-8")
    out_sha = hashlib.sha256(data).hexdigest()
    print(f"checkpoint sha256 {checkpoint_sha}")
    print(f"weights.rs sha256 {out_sha} ({len(data)} bytes)")
    if args.check:
        on_disk = args.out.read_bytes() if args.out.exists() else None
        if on_disk != data:
            print(f"FAIL: {args.out} differs from the generated text", file=sys.stderr)
            return 1
        print(f"check: {args.out} matches")
        return 0
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_bytes(data)
    print(f"wrote {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
