import LcnExec.Mlp.Proofs
import LeanCheckedNetwork.Trained.AllInputs

/-! PILOT, not a gate (see `LcnExec/Mlp/Proofs.lean`): the refinement theorem for the variant of
`rust/mlp`, composed with the kernel-checked theorem of lean-checked-network,
`LeanCheckedNetwork.Trained.adds_mod_113`. -/

open Aeneas Aeneas.Std Result

namespace LcnExec.Mlp

/-- `predict` adds modulo 113: on every in-range pair it returns `ok (some c)` with
`c = (a + b) % 113`. -/
theorem predict_adds_mod_113 (a b : Usize) (ha : a.val < 113) (hb : b.val < 113) :
    ∃ c, mlp.predict a b = ok (some c) ∧ c.val = (a.val + b.val) % 113 := by
  obtain ⟨c, hc, hv⟩ := predict_eq a b ha hb
  exact ⟨c, hc, by rw [hv]; exact LeanCheckedNetwork.Trained.adds_mod_113 a.val ha b.val hb⟩

end LcnExec.Mlp
