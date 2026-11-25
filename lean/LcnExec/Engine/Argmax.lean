import LcnExec.Engine.Projection

open Aeneas Aeneas.Std Result ControlFlow
namespace LcnExec.Engine

theorem argmax_drop (xs : List Int) (i best : Nat) (bv : Int) (hi : i < xs.length) :
    TransformerInt.argmaxFrom (xs.drop i) i best bv =
      if xs[i] > bv then TransformerInt.argmaxFrom (xs.drop (i+1)) (i+1) i xs[i]
      else TransformerInt.argmaxFrom (xs.drop (i+1)) (i+1) best bv := by
  rw [List.drop_eq_getElem_cons hi]
  rfl

/-- The actual scan preserves the model scan of the unvisited suffix. -/
theorem argmax_spec (l : Array I64 113#usize) :
    engine.argmax l ⦃ r => r.val = TransformerInt.argmax (ints l) ∧ r.val < 113 ⦄ := by
  unfold engine.argmax
  step as ⟨first, hfirst⟩
  unfold engine.argmax_loop
  apply loop.spec_decr_nat
    (measure := fun s : Usize × I64 × Usize => 113 - s.2.2.val)
    (inv := fun s : Usize × I64 × Usize =>
      s.1.val < s.2.2.val ∧ s.2.2.val ≤ 113 ∧
      TransformerInt.argmaxFrom ((ints l).drop s.2.2.val) s.2.2.val s.1.val s.2.1.val =
        TransformerInt.argmax (ints l))
  · rintro ⟨best, bv, c⟩ ⟨hbest, hc, heq⟩
    unfold engine.argmax_loop.body
    dsimp only at hbest hc heq ⊢
    simp only [engine.P]
    split
    · have hc113 : c.val < 113 := by scalar_tac
      rw [argmax_drop _ _ _ _ (by simpa [ints] using hc113)] at heq
      step as ⟨v, hv⟩
      have hvi : (ints l)[c.val]'(by simpa [ints] using hc113) = v.val := by simp [ints, hv]
      rw [hvi] at heq
      split
      · rename_i hgt
        have hgt' : v.val > bv.val := by scalar_tac
        rw [ite_eq_left hgt'] at heq
        step as ⟨c1, hc1⟩
        simp only [hc1]
        exact ⟨by omega, by omega, heq, by omega⟩
      · rename_i hle
        have hle' : ¬ v.val > bv.val := by scalar_tac
        rw [ite_eq_right hle'] at heq
        step as ⟨c1, hc1⟩
        simp only [hc1]
        exact ⟨by omega, by omega, heq, by omega⟩
    · have hc113 : c.val = 113 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, by omega⟩
      simpa [hc113, ints, TransformerInt.argmaxFrom] using heq
  · refine ⟨by scalar_tac, by scalar_tac, ?_⟩
    have hcons : ints l = first.val :: (ints l).drop 1 := by
      have hh := List.drop_eq_getElem_cons (l := ints l) (i := 0) (by simp [ints])
      simpa [ints, hfirst] using hh
    conv_rhs => rw [hcons]
    rfl

theorem argmax_eq : ArgmaxStage := by
  intro l
  have h := argmax_spec l
  cases heq : engine.argmax l with
  | ret r => exact ⟨r, rfl, by simpa [heq] using h⟩
  | vis e k => simp [heq] at h
  | div => simp [heq] at h

#print axioms argmax_drop
#print axioms argmax_spec
#print axioms argmax_eq
end LcnExec.Engine
