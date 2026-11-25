import LcnExec.Translated.GeneralEngine
import LcnExec.GeneralEngine.Model

open Aeneas Aeneas.Std Result ControlFlow

namespace LcnExec.GeneralEngine

/-- Exact integer view of a runtime vector. -/
def ints {n : Usize} (x : Array I64 n) : List Int := x.val.map (·.val)

/-- Exact integer view of a runtime stream: one row per position. -/
def ints2 {n : Usize} (x : Array (Array I64 128#usize) n) : List (List Int) :=
  x.val.map ints

/-- Read runtime weights as exact integers. No shape, range or semantic assumptions. -/
def toLayerModel (lw : general_engine.LayerWeights) : GeneralModel.LayerWeights where
  wq := lw.wq.val.map (fun mat => mat.val.map (fun row => row.val.map (·.val)))
  wk := lw.wk.val.map (fun mat => mat.val.map (fun row => row.val.map (·.val)))
  wv := lw.wv.val.map (fun mat => mat.val.map (fun row => row.val.map (·.val)))
  wo := lw.wo.val.map (fun mat => mat.val.map (fun row => row.val.map (·.val)))
  win := lw.win.val.map (fun row => row.val.map (·.val))
  bin := lw.bin.val.map (·.val)
  wout := lw.wout.val.map (fun row => row.val.map (·.val))
  bout := lw.bout.val.map (·.val)

/-- Read runtime weights as the exact integer model of `GeneralModel`. -/
def toGeneralModel (w : general_engine.Weights) : GeneralModel.Weights where
  nLayers := w.n_layers.val
  vocabSize := w.vocab_size.val
  tok := w.tok.val.map (fun row => row.val.map (·.val))
  pos := w.pos.val.map (fun row => row.val.map (·.val))
  layers := w.layers.val.map toLayerModel
  u := w.u.val.map (fun row => row.val.map (·.val))
  expN := w.exp_n.val.map (·.val)
  exp2 := w.exp_2.val.map (·.val)
  exp1 := w.exp_1.val.map (·.val)
  exp0 := w.exp_0.val.map (·.val)

/-- Symmetric integer envelope, including every stored coordinate. -/
def Bounded {n : Usize} (b : Int) (x : Array I64 n) : Prop :=
  ∀ v ∈ x.val, -b ≤ v.val ∧ v.val ≤ b

def MatrixBound {m n : Usize} (b : Int) (x : Array (Array I8 n) m) : Prop :=
  ∀ row ∈ x.val, ∀ v ∈ row.val, -b ≤ v.val ∧ v.val ≤ b

def TensorBound {h m n : Usize} (b : Int) (x : Array (Array (Array I8 n) m) h) : Prop :=
  ∀ mat ∈ x.val, MatrixBound b mat

def TableBound {n : Usize} (x : Array I64 n) : Prop :=
  ∀ v ∈ x.val, 0 ≤ v.val ∧ v.val ≤ 1073741824

/-- Entry bounds for one layer, to be derived from the translated load checker. -/
structure LayerBounds (L : general_engine.LayerWeights) : Prop where
  wq : TensorBound 5 L.wq
  wk : TensorBound 22 L.wk
  wv : TensorBound 106 L.wv
  wo : TensorBound 93 L.wo
  win : MatrixBound 82 L.win
  wout : MatrixBound 74 L.wout
  bin : Bounded 1073741824 L.bin
  bout : Bounded 137438953472 L.bout

/-- Entry bounds for the whole engine, to be derived from the translated load checker,
not assumed by the correctness theorem. -/
structure LoadBounds (W : general_engine.Weights) : Prop where
  tok : MatrixBound 68 W.tok
  pos : MatrixBound 59 W.pos
  layers : ∀ L ∈ W.layers.val, LayerBounds L
  u : MatrixBound 37 W.u
  exp_n : TableBound W.exp_n
  exp_2 : TableBound W.exp_2
  exp_1 : TableBound W.exp_1
  exp_0 : TableBound W.exp_0

/-- The layer bounds of layer `l`, for a valid layer index. -/
theorem layerBounds {W : general_engine.Weights} (hW : LoadBounds W) (l : Usize)
    (hl : l.val < 2) : LayerBounds (W.layers.val[l.val]'(by simpa using hl)) :=
  hW.layers _ (List.getElem_mem _)

/- Frozen integer envelopes, generalized from `pilot/engine/bounds.json`: the causal
softmax denominator ranges over `[2^30, 32 * 2^30]` in place of `[2^30, 3 * 2^30]`, and
every per-layer stage input satisfies the same `[-127, 127]` embedding envelope because
the inter-layer rescale clamps the stream, so each single-stage envelope carries over. -/
namespace Envelope
def embedding : Int := 127
def query : Int := 81280
def key : Int := 357632
def value : Int := 1723136
def score : Int := 930186526720
def score_difference : Int := 1860373053440
def exp_product : Int := 1152921504606846976
def denominator_min : Int := 1073741824
def denominator_max : Int := 34359738368
def numerator : Int := 18014398509481984
def mixed_value : Int := 441122816
def head_output : Int := 1312781500416
def attention : Int := 5251126001664
def residual : Int := 5253256708096
def hidden_pre : Int := 55138457286082560
def hidden : Int := 215384598773760
def mlp_output : Int := 8160491815779172352
def final_numerator : Int := 8161836649496444928
def final_stream : Int := 124539743797248
def logit : Int := 589820226623766528
end Envelope

/-- Every active row of a causal stream satisfies the embedding envelope. -/
def streams (x : Array (Array I64 128#usize) 32#usize) : Prop :=
  ∀ row ∈ x.val, Bounded Envelope.embedding row

end LcnExec.GeneralEngine
