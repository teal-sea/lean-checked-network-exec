import LcnExec.Engine.Correct
import LcnExec.Engine.LoadComplete
import LcnExec.Engine.Trained.Weights

open Aeneas Aeneas.Std Result
namespace LcnExec.Engine

/-- Runtime weights from the hash-pinned checkpoint. -/
def trainedRust : engine.Weights := TrainedData.trainedRust

/-- Every stored value meets the actual translated load check. -/
theorem trained_load_ok : engine.load_check trainedRust = ok true :=
  load_complete trainedRust TrainedData.trained_bounds

/-- Exact equality, including all biases and softmax lookup tables. -/
theorem trained_view : toModel trainedRust = TransformerInt.Gen.weights :=
  TrainedData.trained_view

/-- The universal engine theorem has an accepted trained instance. -/
theorem accepted_weights_nonempty : ∃ W, engine.load_check W = ok true :=
  ⟨trainedRust, trained_load_ok⟩

/-- Conditional only on gate 4's all-input mathematical accuracy theorem.
No gate 4 row modules are imported by this module. -/
theorem trained_engine_adds_of
    (gate4 : ∀ a, a < 113 → ∀ b, b < 113 →
      TransformerInt.predict TransformerInt.Gen.weights a b = some ((a + b) % 113))
    (a b : Usize) (ha : a.val < 113) (hb : b.val < 113) :
    engine.predict trainedRust a b =
      ok (some (Usize.ofNat ((a.val + b.val) % 113) (by scalar_tac))) :=
  compose engine_correct trainedRust TransformerInt.Gen.weights
    trained_load_ok trained_view gate4 a b ha hb

#print axioms trained_load_ok
#print axioms trained_view
#print axioms accepted_weights_nonempty
#print axioms trained_engine_adds_of
end LcnExec.Engine
