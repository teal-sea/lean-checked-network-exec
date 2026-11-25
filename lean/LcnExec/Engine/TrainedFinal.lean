import LcnExec.Engine.Trained
import TransformerInt.Gen.AllRows

open Aeneas Aeneas.Std Result
namespace LcnExec.Engine

/-- The translated Rust engine computes trained modular addition on the full input domain.
This module is staged for the separately authorized dedicated build, not checked on citadel. -/
theorem trained_engine_adds
    (a b : Usize) (ha : a.val < 113) (hb : b.val < 113) :
    engine.predict trainedRust a b =
      ok (some (Usize.ofNat ((a.val + b.val) % 113) (by scalar_tac))) :=
  trained_engine_adds_of TransformerInt.Gen.adds_mod_113 a b ha hb

#print axioms trained_engine_adds
end LcnExec.Engine
