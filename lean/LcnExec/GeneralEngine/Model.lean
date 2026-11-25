/-!
# The general multi-layer causal integer engine, as a function on `Int`

A Lean model of `rust/general_engine/src/lib.rs`: the proved multi-layer causal integer
language-model engine, written as unbounded integer arithmetic. Each definition below has
the name of the Rust function it models and computes the same integers, with the same
scales, the same rounding, and the same causal order.

What stands for what:

| Rust | Lean |
| --- | --- |
| `i64` | `Int`. The Lean model has no overflow; that the Rust has none is a separate fact |
| `[i64; n]` | `List Int` |
| `x >> n` on `i64` | `Int.shiftRight x n`: rounds toward minus infinity |
| `x / y` on `i64` | `Int.tdiv x y`: rounds toward zero, as Rust does |
| `x & 255` on `i64` | `Int.emod x 256`: the low eight bits in two's complement |
| `t[i]` | `nth d t i`, the default `d` when `i` is out of range |

The causal structure: attention at position `p` mixes the value vectors of positions
`0..p` only; between active layers the stream is rescaled (`>> 16`) and clamped to
`[-127, 127]`; after the last active layer the final stream of position `seqLen - 1` is
unembedded over the first `vocabSize` logits and the argmax is the strict first winner.

Arithmetic is written with `Int.add`, `Int.mul`, `Int.sub`, which are `+`, `*`, `-`.
-/
namespace GeneralModel

/-- The weights of one layer, as `rust/general_engine/src/lib.rs` holds them:
`wq`, `wk`, `wv` 4 by 128 by 32, `wo` 4 by 32 by 128, `win` 128 by 512, `bin` 512,
`wout` 512 by 128, `bout` 128. -/
structure LayerWeights where
  wq : List (List (List Int))
  wk : List (List (List Int))
  wv : List (List (List Int))
  wo : List (List (List Int))
  win : List (List Int)
  bin : List Int
  wout : List (List Int)
  bout : List Int

/-- The weights of the whole engine: `tok` 256 by 128, `pos` 32 by 128, `layers` 2
(only `layers[0..nLayers]` active), `u` 128 by 256, `expN` 32, `exp2`, `exp1`, `exp0`
256 each. -/
structure Weights where
  nLayers : Nat
  vocabSize : Nat
  tok : List (List Int)
  pos : List (List Int)
  layers : List LayerWeights
  u : List (List Int)
  expN : List Int
  exp2 : List Int
  exp1 : List Int
  exp0 : List Int

/-- The all-zero layer: every lookup in it yields empty lists, hence zero contributions. -/
def zeroLayer : LayerWeights where
  wq := []
  wk := []
  wv := []
  wo := []
  win := []
  bin := []
  wout := []
  bout := []

/-- A softmax weight of 1, scale 2^24. -/
def ALPHA_ONE : Int := .ofNat 16777216
/-- 2^30, the table value of exp(0). -/
def EXP_ONE : Int := .ofNat 1073741824
/-- The maximum sequence length. -/
def MAX_SEQ : Nat := 32
/-- The maximum number of layers. -/
def MAX_LAYERS : Nat := 2
/-- The full token vocabulary size. -/
def VOCAB : Nat := 256

/-- Entry `n` of a list, `d` if `n` is out of range. -/
def nth {α : Type} (d : α) : List α → Nat → α
  | x :: _, 0 => x
  | _ :: xs, n + 1 => nth d xs n
  | [], _ => d

/-- Entry-by-entry sum, as long as the shorter list. -/
def addV : List Int → List Int → List Int
  | [], _ => []
  | _ :: _, [] => []
  | x :: xs, y :: ys => Int.add x y :: addV xs ys

/-- `c` times every entry. -/
def scale (c : Int) : List Int → List Int
  | [] => []
  | x :: xs => Int.mul c x :: scale c xs

/-- `sum over k of x[k] * w[k]`, a vector of width `n`: entry `i` is `sum over k of x[k] * w[k][i]`. -/
def lincomb (n : Nat) : List Int → List (List Int) → List Int
  | [], _ => List.replicate n (.ofNat 0)
  | _ :: _, [] => List.replicate n (.ofNat 0)
  | x :: xs, r :: rs => addV (scale x r) (lincomb n xs rs)

/-- `sum over k of x[k] * y[k]`. -/
def dot : List Int → List Int → Int
  | [], _ => .ofNat 0
  | _ :: _, [] => .ofNat 0
  | x :: xs, y :: ys => Int.add (Int.mul x y) (dot xs ys)

/-- `embed`: token plus position embedding, scale 2^8. -/
def embed (W : Weights) (tok pos : Nat) : List Int :=
  addV (nth [] W.tok tok) (nth [] W.pos pos)

/-- The zero stream row of the model, the value of every inactive position. -/
def zeroRow : List Int := List.replicate 128 (.ofNat 0)

/-- `embed_all`: the causal initial stream, rows `0..seqLen` and zero rows after. -/
def embedAll (W : Weights) (tokens : List Nat) (seqLen : Nat) : List (List Int) :=
  (List.range MAX_SEQ).map (fun p =>
    if p < seqLen then embed W (nth 0 tokens p) p else zeroRow)

/-- `row_at`: row `p` of a stream, `[]` when `p` is out of range. -/
def rowAt (rows : List (List Int)) (p : Nat) : List Int := nth [] rows p

/-- `project`: a stream vector times a 128 by 32 matrix, scale 2^16. -/
def project (x : List Int) (w : List (List Int)) : List Int := lincomb 32 x w

/-- Layer `l` of the weights, the zero layer when `l` is out of range. -/
def layer (W : Weights) (l : Nat) : LayerWeights := nth zeroLayer W.layers l

/-- One attention score of head `h` at position `p`, scale 2^32:
`(x[p] * wq[h]) . (x[j] * wk[h])`. -/
def keyScore (W : Weights) (l h : Nat) (xp xj : List Int) : Int :=
  dot (project xp (nth [] (layer W l).wq h)) (project xj (nth [] (layer W l).wk h))

/-- `head_scores_at`: the causal attention scores of head `h` of layer `l` read at
position `p`: `s[j]` for `j = 0..p`. -/
def headScoresAt (W : Weights) (l h p : Nat) (rows : List (List Int)) : List Int :=
  (List.range (p + 1)).map (fun j => keyScore W l h (rowAt rows p) (rowAt rows j))

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

/-- The running maximum of the scores `s[0..p]`, as the translated Rust scan computes it. -/
def softmaxMax (s : List Int) (p : Nat) : Int :=
  (List.range (p + 1)).foldl
    (fun m j => if nth 0 s j > m then nth 0 s j else m) (nth 0 s 0)

/-- `softmax_at`: the causal softmax of the scores at position `p`, scale 2^24:
`alpha[j] = e[j] * 2^24 / (sum_{j' <= p} e[j'])` with `e[j] = expFix (smax - s[j])`. -/
def softmaxAt (W : Weights) (s : List Int) (p : Nat) : List Int :=
  let smax := softmaxMax s p
  let es := (List.range (p + 1)).map (fun j => expFix W (Int.sub smax (nth 0 s j)))
  let den := es.foldl Int.add (.ofNat 0)
  es.map (fun e => Int.tdiv (Int.mul e ALPHA_ONE) den)

/-- The value vector `x[j] * wv[h]` of head `h` of layer `l`, scale 2^16. -/
def value (W : Weights) (l h : Nat) (xj : List Int) : List Int :=
  project xj (nth [] (layer W l).wv h)

/-- The mixed value vector of `head_out_at`, scale 2^24:
`z[i] = (sum over j <= p of alpha[j] * v[j][i]) >> 16`. -/
def mixAt (alpha : List Int) (vs : List (List Int)) (p : Nat) : List Int :=
  (List.range 32).map (fun i =>
    Int.shiftRight
      ((List.range (p + 1)).foldl
        (fun acc j => Int.add acc (Int.mul (nth 0 alpha j) (nth 0 (rowAt vs j) i)))
        (.ofNat 0)) 16)

/-- `head_out_at`: what head `h` of layer `l` adds to the residual stream at position `p`,
scale 2^32. -/
def headOutAt (W : Weights) (l h p : Nat) (rows : List (List Int)) (alpha : List Int) :
    List Int :=
  lincomb 128 (mixAt alpha ((List.range (p + 1)).map (fun j => value W l h (rowAt rows j))) p)
    (nth [] (layer W l).wo h)

/-- One pass of the loop of `attention_at`: scores, softmax weights and output of head `h`. -/
def headTermAt (W : Weights) (l h p : Nat) (rows : List (List Int)) : List Int :=
  headOutAt W l h p rows (softmaxAt W (headScoresAt W l h p rows) p)

/-- `attention_at`: the sum of the four heads' outputs at position `p`, scale 2^32. -/
def attentionAt (W : Weights) (l p : Nat) (rows : List (List Int)) : List Int :=
  (List.range 4).foldl
    (fun acc h => addV acc (headTermAt W l h p rows))
    (List.replicate 128 (.ofNat 0))

/-- `residual`: the residual stream after attention, scale 2^32: `x_p * 2^24 + att`. -/
def residual : List Int → List Int → List Int
  | x :: xs, a :: as => Int.add (Int.mul x ALPHA_ONE) a :: residual xs as
  | _, _ => []

/-- The second half of `mlp_hidden`: `pre = acc + bin * 256`, then `pre >> 8` if `pre > 0`,
else 0. -/
def hidden : List Int → List Int → List Int
  | acc :: accs, b :: bs =>
    (let pre := Int.add acc (Int.mul b 256)
     if pre > 0 then Int.shiftRight pre 8 else .ofNat 0) :: hidden accs bs
  | _, _ => []

/-- `mlp_hidden`: the MLP hidden layer of layer `l` after ReLU, scale 2^32. -/
def mlpHidden (W : Weights) (l : Nat) (r : List Int) : List Int :=
  hidden (lincomb 512 r (layer W l).win) (layer W l).bin

/-- `mlp_output`: the MLP output of layer `l`, scale 2^40. -/
def mlpOutput (W : Weights) (l : Nat) (m : List Int) : List Int :=
  addV (lincomb 128 m (layer W l).wout) (layer W l).bout

/-- `final_stream`: the final residual stream, scale 2^24: `(r * 2^8 + o) >> 16`. -/
def finalStream : List Int → List Int → List Int
  | r :: rs, o :: os => Int.shiftRight (Int.add (Int.mul r 256) o) 16 :: finalStream rs os
  | _, _ => []

/-- One position's block output: the scale-2^24 final stream at position `p`. -/
def blockOut (W : Weights) (l p : Nat) (rows : List (List Int)) : List Int :=
  let att := attentionAt W l p rows
  let r := residual (rowAt rows p) att
  finalStream r (mlpOutput W l (mlpHidden W l r))

/-- `layer_forward`: the scale-2^24 final stream of layer `l` at every active position. -/
def layerForward (W : Weights) (l : Nat) (rows : List (List Int)) (seqLen : Nat) :
    List (List Int) :=
  (List.range MAX_SEQ).map (fun p => if p < seqLen then blockOut W l p rows else zeroRow)

/-- `rescale_clamp`: the inter-layer rescale, `s = f[k] >> 16` clamped to `[-127, 127]`. -/
def clampEntry (x : Int) : Int :=
  let s := Int.shiftRight x 16
  if s < -127 then -127 else if s > 127 then 127 else s

def rescaleClamp : List (List Int) → List (List Int) :=
  List.map (List.map clampEntry)

/-- `unembed`: the logits over the full 256-token vocabulary, scale 2^32. -/
def unembed (W : Weights) (fin : List Int) : List Int := lincomb 256 fin W.u

/-- The scan of `argmax` from index `c`; the best so far is at `best` with value `bv`. -/
def argmaxFrom : List Int → Nat → Nat → Int → Nat
  | x :: xs, c, best, bv =>
    if x > bv then argmaxFrom xs (c + 1) c x else argmaxFrom xs (c + 1) best bv
  | [], _, best, _ => best

/-- `argmax`: index of the largest entry among the first `n`, the first one on a tie. -/
def argmaxN (l : List Int) (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => argmaxFrom (List.drop 1 (List.take (k + 1) l)) 1 0 (nth 0 l 0)

/-- The layer stack scan: `runLayers W l r x seqLen last` runs the `r` active layers from
`l` causally over the stream `x`, carrying `last`, the final stream of the last active
layer so far; the final active layer (`l + 1 = nLayers`) writes `rowAt f (seqLen - 1)`
into `last`, every other layer rescales the stream for the next layer. -/
def runLayers (W : Weights) (l : Nat) : Nat → List (List Int) → Nat → List Int → List Int
  | 0, _, _, last => last
  | r + 1, x, seqLen, last =>
      let f := layerForward W l x seqLen
      if l + 1 < W.nLayers then
        runLayers W (l + 1) r (rescaleClamp f) seqLen last
      else
        runLayers W (l + 1) r x seqLen (rowAt f (seqLen - 1))

/-- `forward_logits`: the logits of the full causal forward pass over `seqLen` tokens. -/
def forwardLogits (W : Weights) (tokens : List Nat) (seqLen : Nat) : List Int :=
  unembed W (runLayers W 0 W.nLayers (embedAll W tokens seqLen) seqLen zeroRow)

/-- `predict_next`: `some` of the predicted token for a well-formed input, `none`
otherwise: `1 <= seqLen <= 32`, `1 <= nLayers <= 2`, `1 <= vocabSize <= 256` and
`tokens[p] < 256` for every `p < seqLen`. -/
def predictNext (W : Weights) (tokens : List Nat) (seqLen : Nat) : Option Nat :=
  if seqLen = 0 ∨ seqLen > 32 then none
  else if W.nLayers = 0 ∨ W.nLayers > 2 then none
  else if W.vocabSize = 0 ∨ W.vocabSize > 256 then none
  else if (List.take seqLen tokens).any (fun t => t ≥ 256) then none
  else some (argmaxN (forwardLogits W tokens seqLen) W.vocabSize)

end GeneralModel
