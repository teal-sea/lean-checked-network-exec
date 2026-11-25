import LcnExec.GeneralEngine.Primitives

open Aeneas Aeneas.Std Result ControlFlow

namespace LcnExec.GeneralEngine

private theorem argmax_drop (xs : List Int) (i best : Nat) (bv : Int)
    (hi : i < xs.length) :
    GeneralModel.argmaxFrom (xs.drop i) i best bv =
      if xs[i] > bv then GeneralModel.argmaxFrom (xs.drop (i + 1)) (i + 1) i xs[i]
      else GeneralModel.argmaxFrom (xs.drop (i + 1)) (i + 1) best bv := by
  rw [List.drop_eq_getElem_cons hi]
  rfl

/-- The translated scan visits the supplied vocabulary prefix and retains the first
index at a tie. -/
theorem argmax_spec (l : Array I64 256#usize) (vocab_size : Usize)
    (hvpos : 0 < vocab_size.val) (hvmax : vocab_size.val ≤ 256) :
    general_engine.argmax l vocab_size ⦃ r =>
      r.val = GeneralModel.argmaxN (ints l) vocab_size.val ∧ r.val < vocab_size.val ⦄ := by
  let xs := (ints l).take vocab_size.val
  have hlen : (ints l).length = 256 := by simp [ints]
  have hxs : xs.length = vocab_size.val := by
    dsimp only [xs]
    rw [List.length_take, hlen, Nat.min_eq_left hvmax]
  unfold general_engine.argmax
  step as ⟨first, hfirst⟩
  have hfirstval : GeneralModel.nth 0 (ints l) 0 = first.val := by
    rw [project_nth_eq 0 (ints l) 0 (by rw [hlen]; omega)]
    simp [ints, hfirst]
  have hmodel : GeneralModel.argmaxN (ints l) vocab_size.val =
      GeneralModel.argmaxFrom (xs.drop 1) 1 0 first.val := by
    obtain ⟨n, hn⟩ : ∃ n : Nat, vocab_size.val = n.succ :=
      ⟨vocab_size.val - 1, by omega⟩
    dsimp only [xs]
    rw [hn]
    simp only [GeneralModel.argmaxN, hfirstval]
  unfold general_engine.argmax_loop
  apply loop.spec_decr_nat
    (measure := fun st : Usize × I64 × Usize => vocab_size.val - st.2.2.val)
    (inv := fun st : Usize × I64 × Usize =>
      st.1.val < st.2.2.val ∧ st.2.2.val ≤ vocab_size.val ∧
      GeneralModel.argmaxFrom (xs.drop st.2.2.val) st.2.2.val st.1.val st.2.1.val =
        GeneralModel.argmaxN (ints l) vocab_size.val)
  · rintro ⟨best, bv, c⟩ ⟨hbest, hc, heq⟩
    unfold general_engine.argmax_loop.body
    dsimp only at hbest hc heq ⊢
    split
    · have hcv : c.val < vocab_size.val := by scalar_tac
      have hc256 : c.val < 256 := by omega
      have hcx : c.val < xs.length := by rwa [hxs]
      rw [argmax_drop xs c.val best.val bv.val hcx] at heq
      step as ⟨v, hv⟩
      have hvi : xs[c.val]'hcx = v.val := by
        change ((ints l).take vocab_size.val)[c.val]'hcx = v.val
        rw [List.getElem_take]
        simp only [ints, List.getElem_map]
        rw [hv]
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
    · have hcEnd : c.val = vocab_size.val := by scalar_tac
      have hdrop : xs.drop c.val = [] := by
        rw [hcEnd, ← hxs]
        simp
      simp only [WP.spec_ok]
      refine ⟨?_, by omega⟩
      simpa only [hdrop, GeneralModel.argmaxFrom] using heq
  · refine ⟨by scalar_tac, ?_, ?_⟩
    · change 1 ≤ vocab_size.val
      omega
    · exact hmodel.symm

end LcnExec.GeneralEngine
