import LcnExec.Engine.Contract

open Aeneas Aeneas.Std Result
namespace LcnExec.Engine

/-- Symmetric integer envelope, including every stored coordinate. -/
def Bounded {n : Usize} (b : Int) (x : Array I64 n) : Prop :=
  ∀ v ∈ x.val, -b ≤ v.val ∧ v.val ≤ b

def MatrixBound {m n : Usize} (b : Int) (x : Array (Array I8 n) m) : Prop :=
  ∀ row ∈ x.val, ∀ v ∈ row.val, -b ≤ v.val ∧ v.val ≤ b

def TensorBound {h m n : Usize} (b : Int) (x : Array (Array (Array I8 n) m) h) : Prop :=
  ∀ mat ∈ x.val, MatrixBound b mat

def TableBound {n : Usize} (x : Array I64 n) : Prop :=
  ∀ v ∈ x.val, 0 ≤ v.val ∧ v.val ≤ 1073741824

/-- Entry bounds to be derived from the translated load checker, not assumed by EngineCorrect. -/
structure LoadBounds (W : engine.Weights) : Prop where
  tok : MatrixBound 68 W.tok
  pos : MatrixBound 59 W.pos
  wq : TensorBound 5 W.wq
  wk : TensorBound 22 W.wk
  wv : TensorBound 106 W.wv
  wo : TensorBound 93 W.wo
  win : MatrixBound 82 W.win
  wout : MatrixBound 74 W.wout
  u : MatrixBound 37 W.u
  bin : Bounded 1073741824 W.bin
  bout : Bounded 137438953472 W.bout
  exp_n : TableBound W.exp_n
  exp_2 : TableBound W.exp_2
  exp_1 : TableBound W.exp_1
  exp_0 : TableBound W.exp_0

/- Frozen integer envelopes. Values are the exact entries of pilot/engine/bounds.json. -/
namespace Envelope
def embedding : Int := 127
def query : Int := 81280
def key : Int := 357632
def value : Int := 1723136
def score : Int := 930186526720
def score_difference : Int := 1860373053440
def exp_product : Int := 1152921504606846976
def denominator_min : Int := 1073741824
def denominator_max : Int := 3221225472
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

def streams (x : Array (Array I64 128#usize) 3#usize) : Prop :=
  ∀ row ∈ x.val, Bounded Envelope.embedding row

def triple (x : Array I64 3#usize) : Int × Int × Int :=
  (TransformerInt.nth 0 (ints x) 0, TransformerInt.nth 0 (ints x) 1,
   TransformerInt.nth 0 (ints x) 2)

def stream (x : Array (Array I64 128#usize) 3#usize) (i : Nat) : List Int :=
  TransformerInt.nth [] (x.val.map ints) i

def AlphaBound (a : Array I64 3#usize) : Prop :=
  (∀ v ∈ a.val, 0 ≤ v.val) ∧ (ints a).sum ≤ 16777216

/-- Item 1. -/
def LoadStage : Prop := ∀ W, engine.load_check W = ok true → LoadBounds W

/-- Items 2 and 3. The generic bound also bounds every contraction prefix. -/
def ProjectStage : Prop :=
  ∀ (x : Array I64 128#usize) (w : Array (Array I8 32#usize) 128#usize)
    (bx bw : Int), 0 ≤ bx → 0 ≤ bw → Bounded bx x → MatrixBound bw w →
    128 * bx * bw ≤ Envelope.value →
    ∃ r, engine.project x w = ok r ∧
      ints r = TransformerInt.project (ints x) (w.val.map (fun row => row.val.map (·.val))) ∧
      Bounded (128 * bx * bw) r

def EmbedStage : Prop := ∀ W, LoadBounds W → ∀ t p : Usize, t.val < 114 → p.val < 3 →
  ∃ r, engine.embed W t p = ok r ∧
    ints r = TransformerInt.embed (toModel W) t.val p.val ∧ Bounded Envelope.embedding r

/-- Item 4. -/
def ScoreStage : Prop := ∀ W, LoadBounds W → ∀ (h : Usize)
  (x : Array (Array I64 128#usize) 3#usize), h.val < 4 → streams x →
  ∃ r, engine.head_scores W h x = ok r ∧
    triple r = TransformerInt.headScores (toModel W) h.val (stream x 0) (stream x 1) (stream x 2) ∧
    Bounded Envelope.score r

/-- Items 5 and 6. Exact shifts, casts and masks are part of the exp_fix equality. -/
def ExpStage : Prop := ∀ W, LoadBounds W → ∀ d : I64, 0 ≤ d.val →
  ∃ r, engine.exp_fix W d = ok r ∧ r.val = TransformerInt.expFix (toModel W) d.val ∧
    0 ≤ r.val ∧ r.val ≤ 1073741824

/-- Item 7. Includes the joint bound needed downstream. -/
def SoftmaxStage : Prop := ∀ W, LoadBounds W → ∀ s : Array I64 3#usize,
  Bounded Envelope.score s → ∃ r, engine.softmax_weights W s = ok r ∧
    triple r = TransformerInt.softmaxWeights (toModel W) (triple s) ∧ AlphaBound r

/-- Item 8. -/
def HeadOutputStage : Prop := ∀ W, LoadBounds W → ∀ (h : Usize)
  (x : Array (Array I64 128#usize) 3#usize) (a : Array I64 3#usize),
  h.val < 4 → streams x → AlphaBound a →
  ∃ r, engine.head_output W h x a = ok r ∧
    ints r = TransformerInt.headOutput (toModel W) h.val (stream x 0) (stream x 1) (stream x 2) (triple a) ∧
    Bounded Envelope.head_output r

/-- Item 9, split at the actual Rust stage boundaries. -/
def AttentionStage : Prop := ∀ W, LoadBounds W →
  ∀ x : Array (Array I64 128#usize) 3#usize, streams x →
  ∃ r, engine.attention W x = ok r ∧
    ints r = TransformerInt.attention (toModel W) (stream x 0) (stream x 1) (stream x 2) ∧
    Bounded Envelope.attention r

def ResidualStage : Prop := ∀ x a : Array I64 128#usize,
  Bounded Envelope.embedding x → Bounded Envelope.attention a →
  ∃ r, engine.residual x a = ok r ∧ ints r = TransformerInt.residual (ints x) (ints a) ∧
    Bounded Envelope.residual r

def HiddenStage : Prop := ∀ W, LoadBounds W → ∀ r : Array I64 128#usize,
  Bounded Envelope.residual r → ∃ m, engine.mlp_hidden W r = ok m ∧
    ints m = TransformerInt.mlpHidden (toModel W) (ints r) ∧
    Bounded Envelope.hidden m ∧ ∀ v ∈ m.val, 0 ≤ v.val

def MlpOutputStage : Prop := ∀ W, LoadBounds W → ∀ m : Array I64 512#usize,
  Bounded Envelope.hidden m → ∃ r, engine.mlp_output W m = ok r ∧
    ints r = TransformerInt.mlpOutput (toModel W) (ints m) ∧ Bounded Envelope.mlp_output r

def FinalStage : Prop := ∀ r o : Array I64 128#usize,
  Bounded Envelope.residual r → Bounded Envelope.mlp_output o →
  ∃ f, engine.final_stream r o = ok f ∧
    ints f = TransformerInt.finalStream (ints r) (ints o) ∧ Bounded Envelope.final_stream f

def UnembedStage : Prop := ∀ W, LoadBounds W → ∀ f : Array I64 128#usize,
  Bounded Envelope.final_stream f → ∃ r, engine.unembed W f = ok r ∧
    ints r = TransformerInt.unembed (toModel W) (ints f) ∧ Bounded Envelope.logit r

/-- Item 10. Strict comparison preserves the first winner on ties. -/
def ArgmaxStage : Prop := ∀ l : Array I64 113#usize,
  ∃ r, engine.argmax l = ok r ∧ r.val = TransformerInt.argmax (ints l) ∧ r.val < 113

/-- Item 11. The unchanged target is imported from Contract.lean. -/
def ForwardStage : Prop := ∀ W, engine.load_check W = ok true →
  ∀ a b : Usize, a.val < 113 → b.val < 113 →
  ∃ r, engine.forward W a b = ok r ∧ ints r = TransformerInt.forward (toModel W) a.val b.val

end LcnExec.Engine
