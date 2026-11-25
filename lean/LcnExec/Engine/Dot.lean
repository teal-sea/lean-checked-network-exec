import LcnExec.Translated.Engine
import TransformerInt.Model

open Aeneas Aeneas.Std Result ControlFlow

namespace LcnExec.Engine

/-- Exact integer view of the runtime vector. -/
def ints {n : Usize} (x : Array I64 n) : List Int := x.val.map (·.val)

/-- The bound is above both query and key bounds of the accepted load box. -/
def Small (x : Array I64 32#usize) : Prop :=
  ∀ v ∈ x.val, -1000000 ≤ v.val ∧ v.val ≤ 1000000

theorem dot_drop (xs ys : List Int) (i : Nat) (hx : i < xs.length) (hy : i < ys.length) :
    TransformerInt.dot (xs.drop i) (ys.drop i) =
      xs[i] * ys[i] + TransformerInt.dot (xs.drop (i + 1)) (ys.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hx, List.drop_eq_getElem_cons hy]
  rfl

theorem mul_bound (x y : Int) (hx : -1000000 ≤ x ∧ x ≤ 1000000)
    (hy : -1000000 ≤ y ∧ y ≤ 1000000) :
    -1000000000000 ≤ x * y ∧ x * y ≤ 1000000000000 := by
  constructor <;> nlinarith [mul_nonneg (by omega : 0 ≤ x + 1000000) (by omega : 0 ≤ y + 1000000),
    mul_nonneg (by omega : 0 ≤ 1000000 - x) (by omega : 0 ≤ 1000000 - y),
    mul_nonneg (by omega : 0 ≤ x + 1000000) (by omega : 0 ≤ 1000000 - y),
    mul_nonneg (by omega : 0 ≤ 1000000 - x) (by omega : 0 ≤ y + 1000000)]

/-- Total correctness of the real Rust score dot loop, for arbitrary bounded vectors. -/
theorem dot_spec (x y : Array I64 32#usize) (hx : Small x) (hy : Small y) :
    engine.dot x y ⦃ r => r.val = TransformerInt.dot (ints x) (ints y) ⦄ := by
  unfold engine.dot engine.dot_loop
  apply loop.spec_decr_nat
    (measure := fun (s : I64 × Usize) => 32 - s.2.val)
    (inv := fun (s : I64 × Usize) =>
      s.2.val ≤ 32 ∧
      s.1.val + TransformerInt.dot ((ints x).drop s.2.val) ((ints y).drop s.2.val) =
        TransformerInt.dot (ints x) (ints y) ∧
      -1000000000000 * (s.2.val : Int) ≤ s.1.val ∧
      s.1.val ≤ 1000000000000 * (s.2.val : Int))
  · rintro ⟨acc, i⟩ ⟨hi, hacc, hlo, hhi⟩
    unfold engine.dot_loop.body
    dsimp only at hi hacc hlo hhi ⊢
    split
    · rename_i hlt
      have hi32 : i.val < 32 := by scalar_tac
      rw [dot_drop _ _ _ (by simpa [ints] using hi32) (by simpa [ints] using hi32)] at hacc
      step as ⟨ xv, hxv ⟩
      step as ⟨ yv, hyv ⟩
      have hxs := hx xv (by simp [hxv])
      have hys := hy yv (by simp [hyv])
      have hp := mul_bound xv.val yv.val hxs hys
      step as ⟨ p, hpv ⟩
      step as ⟨ acc1, hacc1 ⟩
      step as ⟨ i1, hi1 ⟩
      have hxi : (ints x)[i.val]'(by simpa [ints] using hi32) = xv.val := by simp [ints, hxv]
      have hyi : (ints y)[i.val]'(by simpa [ints] using hi32) = yv.val := by simp [ints, hyv]
      rw [hxi, hyi] at hacc
      simp only [hi1]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> scalar_tac
    · have hi32 : i.val = 32 := by scalar_tac
      simpa [hi32, ints, TransformerInt.dot] using hacc
  · simp

/-- The returned result is `ok`, not a failure or divergence, and its integer is the model dot. -/
theorem dot_eq (x y : Array I64 32#usize) (hx : Small x) (hy : Small y) :
    ∃ r, engine.dot x y = ok r ∧ r.val = TransformerInt.dot (ints x) (ints y) := by
  have h := dot_spec x y hx hy
  cases heq : engine.dot x y with
  | ret r => exact ⟨r, rfl, by simpa [heq] using h⟩
  | vis i k => simp [heq] at h
  | div => simp [heq] at h

#print axioms dot_eq

end LcnExec.Engine
