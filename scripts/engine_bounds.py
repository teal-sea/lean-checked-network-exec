#!/usr/bin/env python3
"""Conservative integer interval derivation for the explicit engine load box.
This is arithmetic evidence, not a Lean proof of propagation or of load_check.
"""
import json
from pathlib import Path

root = Path(__file__).resolve().parent.parent
x = 68 + 59
q, k, v = (128 * x * weight for weight in (5, 22, 106))
score = 32 * q * k
# alpha_j >= 0 and sum_j alpha_j <= 2^24. A convex weighted sum of
# values in [-v,v], divided by 2^16 and floored, stays in [-256*v,256*v].
z = 256 * v
head = 32 * z * 93
r = x * (1 << 24) + 4 * head
pre = 128 * r * 82 + (1 << 30) * 256
hidden = pre // 256
output = 512 * hidden * 74 + (1 << 37)
final_num = 256 * r + output
final = (final_num + 65535) // 65536
logit = 128 * final * 37
bounds = dict(embedding=x, query=q, key=k, value=v, score=score,
              score_difference=2 * score, exp_product=1 << 60,
              softmax_denominator_min=1 << 30, softmax_denominator_max=3 << 30,
              softmax_numerator=1 << 54, mixed_value=z, head_output=head,
              residual=r, hidden_pre=pre, hidden=hidden, mlp_output=output,
              final_numerator=final_num, final_stream=final, logit=logit,
              i64_max=(1 << 63) - 1)
assert max(bounds.values()) == bounds["i64_max"]
assert all(n < bounds["i64_max"] for name, n in bounds.items() if name != "i64_max")
text = json.dumps(bounds, indent=2) + "\n"
(root / "pilot/engine/bounds.json").write_text(text)
print(text, end="")
