import LcnExec.Translated.Smoke

/-! Step 0 smoke test: one fact about Aeneas's translation of `smoke::sum` (rust/smoke). -/

open Aeneas Aeneas.Std Result ControlFlow

namespace LcnExec.Smoke

/-- A total-correctness triple pins the computation down: it is `ok v` for some `v` satisfying
the postcondition (failure, divergence and effects all make the triple false). -/
theorem eq_ok_of_spec {α : Type} {m : Result α} {p : α → Prop} (h : m ⦃ x => p x ⦄) :
    ∃ v, m = ok v ∧ p v := by
  cases m with
  | ret r => exact ⟨r, rfl, by simpa using h⟩
  | vis i k => simp at h
  | div => simp at h

/-- On a slice whose entries are all zero, the translated loop terminates with `0`. -/
theorem sum_zeros_spec (xs : Slice U32) (hzero : ∀ x ∈ xs.val, x = 0#u32) :
    smoke.sum xs ⦃ r => r = 0#u32 ⦄ := by
  unfold smoke.sum smoke.sum_loop
  apply loop.spec_decr_nat
    (measure := fun (s : U32 × Usize) => xs.length - s.2.val)
    (inv := fun (s : U32 × Usize) => s.1 = 0#u32 ∧ s.2.val ≤ xs.length)
  · rintro ⟨acc, i⟩ ⟨hacc, hi⟩
    unfold smoke.sum_loop.body
    dsimp only at hacc hi ⊢
    split
    · step as ⟨ x, hx ⟩
      have hx0 : x = 0#u32 := hzero x (by simp [hx])
      step as ⟨ acc1, hacc1 ⟩
      step as ⟨ i1, hi1 ⟩
      refine ⟨?_, ?_, ?_⟩ <;> scalar_tac
    · simp [hacc]
  · simp

/-- The smoke fact: on a slice of zeros, the translated `sum` returns `ok 0`. -/
theorem sum_zeros (xs : Slice U32) (hzero : ∀ x ∈ xs.val, x = 0#u32) :
    smoke.sum xs = ok 0#u32 := by
  obtain ⟨v, hv, h0⟩ := eq_ok_of_spec (sum_zeros_spec xs hzero)
  rw [hv, h0]

end LcnExec.Smoke
