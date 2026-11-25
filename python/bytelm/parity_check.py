#!/usr/bin/env python3
"""Cross-language bit-exactness check: ref_engine.py vs the compiled Rust engine.

Runs python/bytelm/rust_parity_check (built with overflow-checks = true, both
profiles) and compares:

1. 200 diverse byte prompts on weights/tiny_bytelm_v1.bin: every one of the
   256 i64 logits of every prompt, Rust vs the exact Python reference.
   (The same 200 prompts are also checked on weights/mod113_v1.bin, where the
   vocab is 113 logits.)
2. weights/mod113_v1.bin: all 12,769 (a, b) pairs, accuracy against
   (a + b) mod 113 and the FNV-1a 64 of all logits, cross-checked with the
   Python sweep in evidence/e5-bytelm/mod113_sweep.txt and the pinned
   rust/transformer fixture.
3. native Rust greedy-generation tokens/sec on the tiny byte LM.

Writes evidence/e5-bytelm/parity.json. Exits nonzero on any mismatch.
"""

import json
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
import ref_engine as re  # noqa: E402

BIN_TINY = ROOT / "weights" / "tiny_bytelm_v1.bin"
BIN_MOD = ROOT / "weights" / "mod113_v1.bin"
EXE = HERE / "rust_parity_check" / "target" / "release" / "rust_parity_check"
SWEEP = ROOT / "evidence" / "e5-bytelm" / "mod113_sweep.txt"
OUT = ROOT / "evidence" / "e5-bytelm" / "parity.json"

N_PROMPTS = 200


def diverse_prompts():
    """200 diverse byte prompts: corpus prefixes, English text, random bytes,
    and structured full-range bytes; lengths from 1 to 32."""
    prompts = []
    lines = (HERE / "corpus.txt").read_text("ascii").split("\n")
    lines = [ln for ln in lines if ln]
    for i in range(70):
        ln = lines[(i * 337) % len(lines)].encode("ascii")
        take = 1 + (i * 7) % 32
        prompts.append(ln[:take])
    hand = [
        b"The capital of France is", b"two plus two is", b"A stitch in time",
        b"What is a proof?", b"Hello. How are you?", b"\n\n", b"  ", b"a",
        b"The quick brown fox", b"0123456789", b"!!! ???", b"mixed CASE Text",
        b"\tTab and\nnewline", b"Paris is spelled P a r", b"zzzzz",
        b"Rome is the capital of Italy.", b"better late than never",
        b"the engine checks every", b"formal verification of the kernel",
        b"the cat sat on the mat",
    ]
    prompts.extend(hand)
    lcg = 0x5EEDC0DE
    while len(prompts) < 140:
        lcg = (lcg * 6364136223846793005 + 1442695040888963407) % (1 << 64)
        n = 1 + (lcg >> 33) % 32
        p = []
        for _ in range(n):
            lcg = (lcg * 6364136223846793005 + 1442695040888963407) % (1 << 64)
            p.append((lcg >> 33) % 256)
        prompts.append(bytes(p))
    for i in range(60):
        n = 1 + (i * 13) % 32
        prompts.append(bytes(((j * 7 + i * 31 + 13) % 256) for j in range(n)))
    assert len(prompts) >= N_PROMPTS
    return prompts[:N_PROMPTS]


def hexline(p):
    return p.hex()


def run(args, stdin_text=None):
    done = subprocess.run([str(EXE)] + args, input=stdin_text,
                          capture_output=True, text=True, check=False)
    if done.returncode != 0:
        raise RuntimeError(f"{EXE} {args} exited {done.returncode}: "
                           f"{done.stderr[-500:]}")
    return done.stdout


def logits_parity(bin_path, prompts):
    """0-mismatch comparison of every logit of every prompt."""
    stdin_text = "\n".join(hexline(p) for p in prompts) + "\n"
    out = run(["logits", str(bin_path)], stdin_text)
    rust_lines = out.strip().split("\n")
    assert len(rust_lines) == len(prompts), \
        f"{len(rust_lines)} rust lines for {len(prompts)} prompts"
    w = re.load(bin_path)
    e = re.Engine(w)
    checked = 0
    mismatches = 0
    t0 = time.time()
    for prompt, rline in zip(prompts, rust_lines):
        parts = rline.split()
        seq_len = int(parts[0])
        rust = [int(v) for v in parts[1:]]
        py = e.forward_logits(list(prompt), seq_len)
        assert py is not None, f"reference rejected prompt {prompt!r}"
        checked += len(py)
        if py != rust:
            mismatches += sum(1 for x, y in zip(py, rust) if x != y) \
                + abs(len(py) - len(rust))
    return checked, mismatches, time.time() - t0


def mod113_check():
    out = run(["mod113", str(BIN_MOD)])
    fields = dict(line.split(" ", 1) for line in out.strip().split("\n"))
    rust = dict(
        pairs=int(fields["pairs"]),
        wrong=int(fields["wrong"]),
        accuracy=fields["accuracy"],
        fnv=fields["logits_fnv1a64"],
    )
    sweep = {}
    for line in SWEEP.read_text().split("\n"):
        if line.startswith("wrong: "):
            sweep["wrong"] = int(line.split()[1].rstrip(";"))
        elif line.startswith("logits FNV-1a 64: "):
            sweep["fnv"] = line.split()[-1]
        elif line.startswith("pairs: "):
            sweep["pairs"] = int(line.split()[1])
    fixture = (ROOT / "rust" / "transformer" / "tests" / "fixtures"
               / "python_reference.txt").read_text()
    pinned = [ln.split()[1] for ln in fixture.split("\n")
              if ln.startswith("logits_fnv1a64 ")][0]
    return rust, sweep, pinned


def bench():
    # 48 prompts x 16 generated tokens = 768 greedy forwards: the harness Rust
    # allocates fresh nested vectors per forward, so a bounded sample measures
    # tokens/sec without a 20-minute run.
    out = run(["bench", str(BIN_TINY), "48"])
    fields = dict(line.split(" ", 1) for line in out.strip().split("\n"))
    return dict(
        prompts=int(fields["prompts"]),
        generated_tokens=int(fields["generated_tokens"]),
        seconds=float(fields["seconds"]),
        tokens_per_second=float(fields["tokens_per_second"]),
    )


def main():
    if not EXE.exists():
        print(f"FAIL: {EXE} not built; run cargo build --release first",
              file=sys.stderr)
        return 1
    prompts = diverse_prompts()
    lens = sorted(len(p) for p in prompts)
    print(f"prompts: {len(prompts)} (length {lens[0]}..{lens[-1]})")

    ok = True
    checked_t, mm_t, secs = logits_parity(BIN_TINY, prompts)
    print(f"tiny_bytelm_v1.bin: {checked_t} logits compared "
          f"({len(prompts)} prompts x 256), {mm_t} mismatches "
          f"(python side {secs:.0f}s)")
    ok &= mm_t == 0

    checked_m, mm_m, _ = logits_parity(BIN_MOD, prompts)
    print(f"mod113_v1.bin: {checked_m} logits compared "
          f"({len(prompts)} prompts x 113), {mm_m} mismatches")
    ok &= mm_m == 0

    rust, sweep, pinned = mod113_check()
    print(f"mod113 rust: wrong {rust['wrong']}, accuracy {rust['accuracy']}, "
          f"fnv {rust['fnv']}")
    print(f"mod113 python sweep: wrong {sweep.get('wrong')}, "
          f"fnv {sweep.get('fnv')}")
    print(f"mod113 pinned rust/transformer fixture fnv: {pinned}")
    ok &= rust["wrong"] == 0 and rust["accuracy"] == "12769/12769"
    ok &= rust["fnv"] == sweep.get("fnv") == pinned

    b = bench()
    print(f"rust bench: {b['generated_tokens']} tokens in {b['seconds']:.3f}s "
          f"= {b['tokens_per_second']:.1f} tokens/sec")

    result = dict(
        exe=str(EXE.relative_to(ROOT)),
        prompts=len(prompts),
        prompt_len_range=[lens[0], lens[-1]],
        tiny_bytelm_logits_compared=checked_t,
        tiny_bytelm_mismatches=mm_t,
        mod113_logits_compared=checked_m,
        mod113_mismatches=mm_m,
        mod113_rust=rust,
        mod113_python_sweep=sweep,
        mod113_pinned_fixture_fnv=pinned,
        rust_bench=b,
        result="PASS" if ok else "FAIL",
    )
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print(f"wrote {OUT.relative_to(ROOT)}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
