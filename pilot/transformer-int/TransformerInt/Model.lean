/-!
# The fixed-width integer transformer, as a function on `Int`

A Lean model of `rust/transformer/src/lib.rs`: the trained one-layer, four-head transformer on
addition mod 113, written as integer arithmetic. Each definition below has the name of the Rust
function it models and computes the same integers, with the same scale and the same rounding.

What stands for what:

| Rust | Lean |
| --- | --- |
| `i64` | `Int`. The Lean model has no overflow; that the Rust has none is a separate fact |
| `[i64; n]` | `List Int` |
| `x >> n` on `i64` | `Int.shiftRight x n`: rounds toward minus infinity |
| `x / y` on `i64` | `Int.tdiv x y`: rounds toward zero, as Rust does |
| `x & 255` on `i64` | `Int.emod x 256`: the low eight bits in two's complement |
| `t[i]` | `nth d t i`, the default `d` when `i` is out of range |

A matrix product `out[i] = sum over k of x[k] * w[k][i]` is `lincomb n x w`, the sum of the rows
`w[k]` weighted by `x[k]`. The Rust adds the terms in the order `k = 0, 1, ...` for each `i`;
on `Int` the order does not change the sum.

Arithmetic is written with `Int.add`, `Int.mul`, `Int.sub`, which are `+`, `*`, `-`; spelling
them out keeps Lean's kernel from unfolding the notation at every step.
-/

namespace TransformerInt

/-- The weights and the four exponential tables, as `rust/transformer/src/weights.rs` holds them.
`tok` 114 by 128, `pos` 3 by 128, `wq`, `wk`, `wv` 4 by 128 by 32, `wo` 4 by 32 by 128,
`win` 128 by 512, `bin` 512, `wout` 512 by 128, `bout` 128, `u` 128 by 113,
`expN` 32, `exp2`, `exp1`, `exp0` 256 each. -/
structure Weights where
  tok : List (List Int)
  pos : List (List Int)
  wq : List (List (List Int))
  wk : List (List (List Int))
  wv : List (List (List Int))
  wo : List (List (List Int))
  win : List (List Int)
  bin : List Int
  wout : List (List Int)
  bout : List Int
  u : List (List Int)
  expN : List Int
  exp2 : List Int
  exp1 : List Int
  exp0 : List Int

/-- The modulus. Inputs and answers are `0..113`. -/
def P : Nat := 113
/-- The token `=`. -/
def EQ : Nat := 113
/-- A softmax weight of 1, scale 2^24. -/
def ALPHA_ONE : Int := .ofNat 16777216
/-- 2^30, the table value of exp(0). -/
def EXP_ONE : Int := .ofNat 1073741824

/-- Entry `n` of a list, `d` if `n` is out of range. -/
def nth {α : Type} (d : α) : List α → Nat → α
  | x :: _, 0 => x
  | _ :: xs, n + 1 => nth d xs n
  | [], _ => d

/-- Entry-by-entry sum, as long as the shorter list. -/
def addV : List Int → List Int → List Int
  | x :: xs, y :: ys => Int.add x y :: addV xs ys
  | _, _ => []

/-- `c` times every entry. -/
def scale (c : Int) : List Int → List Int
  | [] => []
  | x :: xs => Int.mul c x :: scale c xs

/-- `sum over k of x[k] * w[k]`, a vector of width `n`: entry `i` is `sum over k of x[k] * w[k][i]`. -/
def lincomb (n : Nat) : List Int → List (List Int) → List Int
  | x :: xs, r :: rs => addV (scale x r) (lincomb n xs rs)
  | _, _ => List.replicate n (.ofNat 0)

/-- `sum over k of x[k] * y[k]`. -/
def dot : List Int → List Int → Int
  | x :: xs, y :: ys => Int.add (Int.mul x y) (dot xs ys)
  | _, _ => .ofNat 0

/-- `embed`: token plus position embedding, scale 2^8. -/
def embed (W : Weights) (tok pos : Nat) : List Int :=
  addV (nth [] W.tok tok) (nth [] W.pos pos)

/-- `project`: a stream vector times a 128 by 32 matrix, scale 2^16. -/
def project (x : List Int) (w : List (List Int)) : List Int := lincomb 32 x w

/-- One attention score of head `h`, scale 2^32: `(x2 * WQ[h]) . (xj * WK[h])`. -/
def keyScore (W : Weights) (h : Nat) (x2 xj : List Int) : Int :=
  dot (project x2 (nth [] W.wq h)) (project xj (nth [] W.wk h))

/-- `head_scores`: the three attention scores of head `h`, read at the last position. -/
def headScores (W : Weights) (h : Nat) (x0 x1 x2 : List Int) : Int × Int × Int :=
  (keyScore W h x2 x0, keyScore W h x2 x1, keyScore W h x2 x2)

/-- `exp_fix`: the integer stand-in for `2^30 * exp(-d / 2^32)`, from four tables. -/
def expFix (W : Weights) (d : Int) : Int :=
  if d ≤ 0 then EXP_ONE
  else
    let u := Int.shiftRight d 8
    let n := Int.shiftRight u 24
    if 32 ≤ n then .ofNat 0
    else
      let b2 := Int.emod (Int.shiftRight u 16) 256
      let b1 := Int.emod (Int.shiftRight u 8) 256
      let b0 := Int.emod u 256
      let e := nth 0 W.expN (Int.toNat n)
      let e := Int.shiftRight (Int.mul e (nth 0 W.exp2 (Int.toNat b2))) 30
      let e := Int.shiftRight (Int.mul e (nth 0 W.exp1 (Int.toNat b1))) 30
      Int.shiftRight (Int.mul e (nth 0 W.exp0 (Int.toNat b0))) 30

/-- `softmax_weights`: the softmax of three scores, scale 2^24. -/
def softmaxWeights (W : Weights) (s : Int × Int × Int) : Int × Int × Int :=
  let smax := s.1
  let smax := if s.2.1 > smax then s.2.1 else smax
  let smax := if s.2.2 > smax then s.2.2 else smax
  let e0 := expFix W (Int.sub smax s.1)
  let e1 := expFix W (Int.sub smax s.2.1)
  let e2 := expFix W (Int.sub smax s.2.2)
  let den := Int.add (Int.add e0 e1) e2
  (Int.tdiv (Int.mul e0 ALPHA_ONE) den, Int.tdiv (Int.mul e1 ALPHA_ONE) den,
    Int.tdiv (Int.mul e2 ALPHA_ONE) den)

/-- The mixed value vector of `head_output`, scale 2^24:
`z[i] = (a0 * v0[i] + a1 * v1[i] + a2 * v2[i]) >> 16`. -/
def mix (a0 a1 a2 : Int) : List Int → List Int → List Int → List Int
  | v0 :: r0, v1 :: r1, v2 :: r2 =>
    Int.shiftRight (Int.add (Int.add (Int.mul a0 v0) (Int.mul a1 v1)) (Int.mul a2 v2)) 16
      :: mix a0 a1 a2 r0 r1 r2
  | _, _, _ => []

/-- The value vector `xj * WV[h]` of head `h`, scale 2^16. -/
def value (W : Weights) (h : Nat) (xj : List Int) : List Int := project xj (nth [] W.wv h)

/-- `head_output`: what head `h` adds to the residual stream, scale 2^32. -/
def headOutput (W : Weights) (h : Nat) (x0 x1 x2 : List Int) (alpha : Int × Int × Int) :
    List Int :=
  lincomb 128 (mix alpha.1 alpha.2.1 alpha.2.2 (value W h x0) (value W h x1) (value W h x2))
    (nth [] W.wo h)

/-- One pass of the loop of `attention`: scores, softmax weights and output of head `h`. -/
def headTerm (W : Weights) (h : Nat) (x0 x1 x2 : List Int) : List Int :=
  headOutput W h x0 x1 x2 (softmaxWeights W (headScores W h x0 x1 x2))

/-- `attention`: the sum of the four heads' outputs, scale 2^32. -/
def attention (W : Weights) (x0 x1 x2 : List Int) : List Int :=
  addV (addV (addV (addV (List.replicate 128 (.ofNat 0)) (headTerm W 0 x0 x1 x2))
    (headTerm W 1 x0 x1 x2)) (headTerm W 2 x0 x1 x2)) (headTerm W 3 x0 x1 x2)

/-- `residual`: the residual stream after attention, scale 2^32: `x2 * 2^24 + att`. -/
def residual : List Int → List Int → List Int
  | x :: xs, a :: as => Int.add (Int.mul x ALPHA_ONE) a :: residual xs as
  | _, _ => []

/-- The second half of `mlp_hidden`: `pre = acc + bin * 256`, then `pre >> 8` if `pre > 0`, else 0. -/
def hidden : List Int → List Int → List Int
  | acc :: accs, b :: bs =>
    (let pre := Int.add acc (Int.mul b 256)
     if pre > 0 then Int.shiftRight pre 8 else .ofNat 0) :: hidden accs bs
  | _, _ => []

/-- `mlp_hidden`: the MLP hidden layer after ReLU, scale 2^32. -/
def mlpHidden (W : Weights) (r : List Int) : List Int := hidden (lincomb 512 r W.win) W.bin

/-- `mlp_output`: the MLP output, scale 2^40. -/
def mlpOutput (W : Weights) (m : List Int) : List Int := addV (lincomb 128 m W.wout) W.bout

/-- `final_stream`: the final residual stream, scale 2^24: `(r * 2^8 + o) >> 16`. -/
def finalStream : List Int → List Int → List Int
  | r :: rs, o :: os => Int.shiftRight (Int.add (Int.mul r 256) o) 16 :: finalStream rs os
  | _, _ => []

/-- `unembed`: the 113 logits, scale 2^32. -/
def unembed (W : Weights) (fin : List Int) : List Int := lincomb 113 fin W.u

/-- The scan of `argmax` from index `c`; the best so far is at `best` with value `bv`. -/
def argmaxFrom : List Int → Nat → Nat → Int → Nat
  | x :: xs, c, best, bv =>
    if x > bv then argmaxFrom xs (c + 1) c x else argmaxFrom xs (c + 1) best bv
  | [], _, best, _ => best

/-- `argmax`: index of the largest entry, the first one on a tie. -/
def argmax : List Int → Nat
  | x :: xs => argmaxFrom xs 1 0 x
  | [] => 0

/-- `forward`: the logits for the tokens `[a, b, =]`, scale 2^32. -/
def forward (W : Weights) (a b : Nat) : List Int :=
  let x0 := embed W a 0
  let x1 := embed W b 1
  let x2 := embed W EQ 2
  let r := residual x2 (attention W x0 x1 x2)
  unembed W (finalStream r (mlpOutput W (mlpHidden W r)))

/-- `logits`: `some` of the logits for `a, b < 113`, `none` otherwise. -/
def logits (W : Weights) (a b : Nat) : Option (List Int) :=
  if a ≥ P ∨ b ≥ P then none else some (forward W a b)

/-- `predict`: `some` of the answer for `a, b < 113`, `none` otherwise. -/
def predict (W : Weights) (a b : Nat) : Option Nat :=
  if a ≥ P ∨ b ≥ P then none else some (argmax (forward W a b))

end TransformerInt
