import LcnExec.Engine.View

open Aeneas Aeneas.Std Result
namespace LcnExec.Engine

/-- The exact universal engine goal. The existential is only the machine representation of
an answer: its `val` is required to be precisely the model's answer. No overflow, failure,
or divergence is permitted. Load success is a computation of the translated Rust checker,
not an unchecked predicate supplied by a caller. -/
def EngineCorrect : Prop :=
  ∀ (W : engine.Weights), engine.load_check W = ok true →
    ∀ (a b : Usize), a.val < 113 → b.val < 113 →
      ∃ r : Usize, engine.predict W a b = ok (some r) ∧
        TransformerInt.predict (toModel W) a.val b.val = some r.val

/-- Composing the engine goal with a model theorem requires exact weights and load success.
This is proved, but does not discharge any of those hypotheses. -/
theorem compose (engine_correct : EngineCorrect) (rustWeights : engine.Weights)
    (modelWeights : TransformerInt.Weights)
    (load_ok : engine.load_check rustWeights = ok true)
    (weights_eq : toModel rustWeights = modelWeights)
    (model_correct : ∀ a, a < 113 → ∀ b, b < 113 →
      TransformerInt.predict modelWeights a b = some ((a + b) % 113))
    (a b : Usize) (ha : a.val < 113) (hb : b.val < 113) :
    engine.predict rustWeights a b =
      ok (some (Usize.ofNat ((a.val + b.val) % 113) (by scalar_tac))) := by
  obtain ⟨r, hr, hmodel⟩ := engine_correct rustWeights load_ok a b ha hb
  rw [weights_eq, model_correct a.val ha b.val hb] at hmodel
  have hv : r.val = (a.val + b.val) % 113 := (Option.some.inj hmodel).symm
  rw [hr]
  congr 2
  scalar_tac

#print axioms compose
end LcnExec.Engine
