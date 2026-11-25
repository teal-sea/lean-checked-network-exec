#!/usr/bin/env python3
"""Verify weights/mod113_v1.bin: 12,769 / 12,769 exact accuracy, all pairs.

Runs the exact integer engine of ref_engine.py on every (a, b) in 0..113 x
0..113 with tokens [a, b, 113] (the `=` token), checks predict_next against
(a + b) mod 113, and hashes all logits (FNV-1a 64, the layout of
scripts/check_transformer_int.py) to compare with the pinned fixture of
rust/transformer. Writes evidence/e5-bytelm/mod113_sweep.txt.
"""

import struct
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ref_engine as re  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
BIN = ROOT / "weights" / "mod113_v1.bin"
FIXTURE = ROOT / "rust" / "transformer" / "tests" / "fixtures" / "python_reference.txt"
OUT = ROOT / "evidence" / "e5-bytelm" / "mod113_sweep.txt"

P = 113
EQ = 113


def fnv1a64(data, state):
    for byte in data:
        state = ((state ^ byte) * 0x100000001B3) & 0xFFFFFFFFFFFFFFFF
    return state


def main():
    w = re.load(BIN)
    lines = []
    say = lambda s="": (print(s, flush=True), lines.append(s))
    say(f"file: {BIN.name} ({BIN.stat().st_size} bytes), load_check {re.load_check(w)}")
    e = re.Engine(w)
    wrong = 0
    ties = 0
    min_margin = None
    min_pair = None
    state = 0xCBF29CE484222325
    t0 = time.time()
    for a in range(P):
        for b in range(P):
            out = e.forward_logits([a, b, EQ], 3)
            assert out is not None and len(out) == P
            label = (a + b) % P
            best, best_value = 0, out[0]
            for c in range(1, P):
                if out[c] > best_value:
                    best_value, best = out[c], c
            if best != label:
                wrong += 1
            margin = out[label] - max(out[c] for c in range(P) if c != label)
            if margin == 0:
                ties += 1
            if min_margin is None or margin < min_margin:
                min_margin, min_pair = margin, (a, b)
            state = fnv1a64(struct.pack(f"<{P}q", *out), state)
    secs = time.time() - t0
    say(f"pairs: {P * P} in {secs:.0f} s")
    say(f"wrong: {wrong}; ties: {ties}")
    say(f"smallest margin: {min_margin} at pair {min_pair}")
    say(f"logits FNV-1a 64: {state:016x}")
    ok = wrong == 0
    if FIXTURE.exists():
        pinned = None
        for line in FIXTURE.read_text().splitlines():
            if line.startswith("logits_fnv1a64 "):
                pinned = line.split()[1]
        say(f"fixture logits_fnv1a64 (rust/transformer): {pinned}")
        say(f"logit hash matches the pinned rust/transformer fixture: "
            f"{'yes' if pinned == f'{state:016x}' else 'NO'}")
        ok &= pinned == f"{state:016x}"
    else:
        say("fixture: not found, hash not compared")
    say(f"result: {'PASS' if ok else 'FAIL'}")
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text("\n".join(lines) + "\n")
    print(f"wrote {OUT.relative_to(ROOT)}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
