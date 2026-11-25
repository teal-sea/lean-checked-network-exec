import LcnExec.GeneralEngine.Attention

open Aeneas Aeneas.Std Result ControlFlow

namespace LcnExec.GeneralEngine

theorem head_out_row_copy_spec (vs : Array (Array I64 32#usize) 32#usize)
    (j : Usize) (hj : j.val < 32) (v : Array I64 32#usize) :
    general_engine.head_out_at_loop0_loop0 vs j v 0#usize ⦃ r =>
      r = Std.Array.set vs j v ⦄ := by
  unfold general_engine.head_out_at_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (st : Array (Array I64 32#usize) 32#usize × Usize) => 32 - st.2.val)
    (inv := fun (st : Array (Array I64 32#usize) 32#usize × Usize) =>
      st.2.val ≤ 32 ∧
      (∀ (k : Nat) (hk : k < 32) (hik : k < st.2.val),
        (st.1.val[j.val]'(by simp; omega)).val[k]'(by simp; omega) =
          v.val[k]'(by simp; omega)) ∧
      (∀ (k : Nat) (hk : k < 32) (hik : st.2.val ≤ k),
        (st.1.val[j.val]'(by simp; omega)).val[k]'(by simp; omega) =
          (vs.val[j.val]'(by simp; omega)).val[k]'(by simp; omega)) ∧
      (∀ (j' : Nat) (hj' : j' < 32) (hne : j' ≠ j.val),
        st.1.val[j']'(by simp; omega) = vs.val[j']'(by simp; omega)))
  · rintro ⟨vs', i⟩ ⟨hi1, hpre, hsuf, hoth⟩
    unfold general_engine.head_out_at_loop0_loop0.body
    dsimp only at hi1 hpre hsuf hoth ⊢
    simp only [general_engine.D_HEAD]
    split
    · have hi32 : i.val < 32 := by scalar_tac
      step with Array.index_usize_spec v i (by simp; omega) as ⟨i1, hi1v⟩
      step with Array.index_mut_usize_spec vs' j (by simp; omega) as ⟨a, back, ha, hback⟩
      step with Array.update_spec a i i1 (by simp; omega) as ⟨a1, ha1⟩
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = i.val + 1 := by scalar_tac
      simp only [hi2]
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · intro k hk hik
        simp only [hback, ha1, ha, Array.set_val_eq]
        by_cases hki : k = i.val
        · subst k
          simp [List.getElem_set_self, hi1v]
        · simp [List.getElem_set_ne (show i.val ≠ k by omega)]
          exact hpre k hk (by omega)
      · intro k hk hik
        simp only [hback, ha1, ha, Array.set_val_eq]
        simp [List.getElem_set_ne (show i.val ≠ k by omega)]
        exact hsuf k hk (by omega)
      · intro j' hj' hne
        simp only [hback, Array.set_val_eq]
        rw [List.getElem_set_ne (by omega)]
        exact hoth j' hj' hne
    · have hi32 : i.val = 32 := by scalar_tac
      simp only [WP.spec_ok]
      refine (Array.eq_iff _ _).mpr ?_
      apply List.ext_getElem
      · simp [Array.set_val_eq]
      · intro j' hj' hj''
        by_cases hjj : j' = j.val
        · subst j'
          simp only [Array.set_val_eq, List.getElem_set_self]
          refine (Array.eq_iff _ _).mpr ?_
          apply List.ext_getElem
          · simp
          · intro k hk hk'
            have hk32 : k < 32 := by simpa using hk
            exact hpre k hk32 (by omega)
        · simp only [Array.set_val_eq]
          rw [List.getElem_set_ne (by omega)]
          exact hoth j' (by simpa using hj') (by omega)
  · simp only
    refine ⟨by scalar_tac, ?_, ?_, ?_⟩
    · intro k hk hik
      exact absurd hik (by show ¬(k < 0); omega)
    · intro k hk hik
      trivial
    · intro j' hj' hne
      trivial

end LcnExec.GeneralEngine
