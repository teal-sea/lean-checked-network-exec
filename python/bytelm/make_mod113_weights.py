#!/usr/bin/env python3
"""Build `weights/mod113_v1.bin` (GLMW v1) from the repo's trained mod-113 weights.

Source of the integers: `rust/transformer/src/weights.rs`, the generated file that
holds the quantised one-layer mod-113 model of `rust/transformer` (checkpoint
sha256 7cea95ed..., see scripts/gen_transformer_weights.py). The arrays are
parsed from the Rust literals, so no checkpoint file or numpy is needed.

Mapping into the general engine (SPEC-E4-E6.md section 4, "Mod-113 Equivalence"):

- n_layers = 1, vocab_size = 113; the second layer is all zeros.
- tok rows 0..113 are the 114 rows of TOK (0..112 plus the `=` token 113);
  rows 114..255 are zero.
- pos rows 0..2 are the 3 rows of POS; rows 3..31 are zero.
- Layer 0 carries WQ, WK, WV, WO, WIN, BIN, WOUT, BOUT unchanged.
- u columns 0..112 are the 113 columns of U; columns 113..255 are zero.

The forward of `ref_engine.Engine` on tokens `[a, b, 113]`, seq_len 3, then
matches `rust/transformer` bit for bit (verified by verify_mod113.py and by the
Rust parity check).
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ref_engine as re  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
WEIGHTS_RS = ROOT / "rust" / "transformer" / "src" / "weights.rs"
OUT = ROOT / "weights" / "mod113_v1.bin"

D_MODEL, N_HEADS, D_HEAD, D_MLP = 128, 4, 32, 512

NAMES = ("TOK", "POS", "WQ", "WK", "WV", "WO", "WIN", "BIN", "WOUT", "BOUT",
         "U", "EXP_N", "EXP_2", "EXP_1", "EXP_0")


def parse_rust_arrays(text):
    """Every `pub static NAME: ... = [ ... ];` of weights.rs as nested lists."""
    out = {}
    for name in NAMES:
        start = text.index(f"pub static {name}:")
        eq = text.index("= [", start) + 2  # at the '['
        end = text.index("\n];", eq)
        body = text[eq:end + 2]  # through the closing ']'
        stack = [[]]
        num = ""
        for ch in body:
            if ch.isdigit() or (ch == "-" and not num):
                num += ch
                continue
            if num:
                stack[-1].append(int(num))
                num = ""
            if ch == "[":
                stack.append([])
            elif ch == "]":
                top = stack.pop()
                stack[-1].append(top)
        if num:
            stack[-1].append(int(num))
        out[name] = stack[0][0]
        assert out[name], name
    return out


def pad_rows(rows, n_rows, width):
    """rows -> n_rows lists of length width, zero-padded."""
    assert len(rows) <= n_rows
    out = [list(r) for r in rows]
    while len(out) < n_rows:
        out.append([0] * width)
    return out


def build():
    text = WEIGHTS_RS.read_text()
    a = parse_rust_arrays(text)

    tok = pad_rows(a["TOK"], 256, D_MODEL)          # 114 rows -> 256
    pos = pad_rows(a["POS"], 32, D_MODEL)           # 3 rows -> 32
    u = [list(row) + [0] * (256 - len(row)) for row in a["U"]]  # 113 cols -> 256

    layer0 = re.LayerWeights(
        [ [ [a["WQ"][h][k][i] for i in range(D_HEAD)] for k in range(D_MODEL)] for h in range(N_HEADS)],
        [ [ [a["WK"][h][k][i] for i in range(D_HEAD)] for k in range(D_MODEL)] for h in range(N_HEADS)],
        [ [ [a["WV"][h][k][i] for i in range(D_HEAD)] for k in range(D_MODEL)] for h in range(N_HEADS)],
        [ [ [a["WO"][h][t][k] for k in range(D_MODEL)] for t in range(D_HEAD)] for h in range(N_HEADS)],
        [list(row) for row in a["WIN"]],
        list(a["BIN"]),
        [list(row) for row in a["WOUT"]],
        list(a["BOUT"]),
    )
    w = re.Weights(1, 113, tok, pos, [layer0, re.LayerWeights()], u,
                   list(a["EXP_N"]), list(a["EXP_2"]), list(a["EXP_1"]),
                   list(a["EXP_0"]))
    return w


def main():
    w = build()
    if not re.load_check(w):
        print("FAIL: load_check is False")
        return 1
    data = re.pack(w)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_bytes(data)
    print(f"wrote {OUT} ({len(data)} bytes)")
    w2 = re.load(OUT)
    print(f"round-trip load_check: {re.load_check(w2)}")
    e = re.Engine(w2)
    ok = True
    for a_, b_ in ((0, 0), (21, 56), (57, 111), (112, 112), (60, 60)):
        got = e.predict_next([a_, b_, 113], 3)
        want = (a_ + b_) % 113
        flag = "ok" if got == want else "WRONG"
        ok &= got == want
        print(f"  ({a_}, {b_}) -> {got}, want {want}: {flag}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
