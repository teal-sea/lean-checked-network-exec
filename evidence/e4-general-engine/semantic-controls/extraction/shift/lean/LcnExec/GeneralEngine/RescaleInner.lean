import LcnExec.GeneralEngine.LayerForward

set_option maxHeartbeats 800000

/-!
# The inter-layer rescale `general_engine.rescale_clamp`

Per entry `s = f[p][k] >>> 16` clamped to [-127, 127]. Exact
`GeneralModel.rescaleClamp` (= `List.map (List.map clampEntry)`).
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace LcnExec.GeneralEngine

theorem clamp_entry_spec (x : Int) :
    (if Int.shiftRight x 16 < -127 then -127
     else if Int.shiftRight x 16 > 127 then 127
     else Int.shiftRight x 16) = GeneralModel.clampEntry x := by
  simp only [GeneralModel.clampEntry]

theorem rescale_clamp_inner_spec (f : Array (Array I64 128#usize) 32#usize)
    (hfb : ∀ row ∈ f.val, Bounded Envelope.final_stream row)
    (p : Usize) (hp : p.val < 32) :
    general_engine.rescale_clamp_loop0_loop0 f p
        (Array.repeat 128#usize 0#i64) 0#usize ⦃ r =>
      ints r = ((ints2 f)[p.val]!).map GeneralModel.clampEntry ∧
      Bounded Envelope.embedding r ⦄ := by
  have hrowf : f.val[p.val]'(by simp; omega) ∈ f.val :=
    List.getElem_mem (by simp; omega)
  have hfbrow : Bounded Envelope.final_stream (f.val[p.val]'(by simp; omega)) :=
    hfb _ hrowf
  let mrow := (ints2 f)[p.val]!
  have hmid : mrow = ints (f.val[p.val]'(by simp; omega)) := by
    unfold mrow
    rw [getElem!_pos (ints2 f) p.val (by rwa [ints2_length])]
    simp [ints2]
  have hmrow_len : mrow.length = 128 := by rw [hmid, ints_length128]
  unfold general_engine.rescale_clamp_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (st : Array I64 128#usize × Usize) => 128 - st.2.val)
    (inv := fun (st : Array I64 128#usize × Usize) =>
      st.2.val ≤ 128 ∧
      (∀ (q : Nat) (hq : q < 128) (hiq : q < st.2.val),
        (ints st.1)[q]'(by rw [ints_length128]; omega) =
          GeneralModel.clampEntry mrow[q]!) ∧
      (∀ (q : Nat) (hq : q < 128) (hiq : st.2.val ≤ q),
        st.1.val[q]'(by simp; omega) = 0#i64) ∧
      Bounded Envelope.embedding st.1)
  · rintro ⟨row1, k⟩ ⟨hk1, heq, hsuf, hbd⟩
    unfold general_engine.rescale_clamp_loop0_loop0.body
    dsimp only at hk1 heq hsuf hbd ⊢
    simp only [general_engine.D_MODEL]
    split
    · have hk128 : k.val < 128 := by scalar_tac
      step as ⟨a, ha⟩
      step as ⟨iv, hiv⟩
      step as ⟨s, hs⟩
      have hsval : s.val = Int.shiftRight iv.val 16 := hs
      have hentry : mrow[k.val]! = iv.val := by
        rw [hmid, getElem!_pos (ints (f.val[p.val]'(by simp; omega))) k.val
          (by rwa [ints_length128])]
        simp only [ints, List.getElem_map]
        subst ha
        rw [hiv]
      have hwrite : ∀ (v : I64) (row2 : Array I64 128#usize)
          (hrow2 : row2 = row1.set k v)
          (hm : GeneralModel.clampEntry mrow[k.val]! = v.val)
          (hv127 : -127 ≤ v.val ∧ v.val ≤ 127),
          (∀ (q : Nat) (hq : q < 128) (hiq : q < k.val + 1),
            (ints row2)[q]'(by rw [ints_length128]; omega) =
              GeneralModel.clampEntry mrow[q]!) ∧
          (∀ (q : Nat) (hq : q < 128) (hiq : k.val + 1 ≤ q),
            row2.val[q]'(by simp; omega) = 0#i64) ∧
          Bounded Envelope.embedding row2 := by
        intro v row2 hrow2 hm hv127
        constructor
        · intro q hq hiq
          by_cases hqq : q = k.val
          · subst q
            have hset : (ints row2)[k.val]'(by rw [ints_length128]; omega) =
                v.val := by
              rw [hrow2]
              simp only [ints, Array.set_val_eq, List.getElem_map]
              rw [List.getElem_set_self (by simp; omega)]
            rw [hset, hm]
          · have hval : (ints row2)[q]'(by rw [ints_length128]; omega) =
                (ints row1)[q]'(by rw [ints_length128]; omega) := by
              rw [hrow2]
              simp only [ints, Array.set_val_eq, List.getElem_map]
              rw [List.getElem_set_ne (by omega)]
            rw [hval]
            exact heq q hq (by omega)
        · constructor
          · intro q hq hiq
            have hval : row2.val[q]'(by simp; omega) =
                row1.val[q]'(by simp; omega) := by
              subst hrow2
              simp only [Array.set_val_eq]
              rw [List.getElem_set_ne (by omega)]
            rw [hval]
            exact hsuf q hq (by omega)
          · rw [hrow2]
            exact project_bounded_set _ _ _ _ hbd hv127
      have hfinish : ∀ (v : I64) (row2 : Array I64 128#usize)
          (hrow2 : row2 = row1.set k v)
          (hm : GeneralModel.clampEntry mrow[k.val]! = v.val)
          (hv127 : -127 ≤ v.val ∧ v.val ≤ 127),
          ((k.val + 1 : Nat) ≤ 128 ∧
            (∀ (q : Nat) (hq : q < 128) (hiq : q < k.val + 1),
              (ints row2)[q]'(by rw [ints_length128]; omega) =
                GeneralModel.clampEntry mrow[q]!) ∧
            (∀ (q : Nat) (hq : q < 128) (hiq : k.val + 1 ≤ q),
              row2.val[q]'(by simp; omega) = 0#i64) ∧
            Bounded Envelope.embedding row2 ∧
            128 - (k.val + 1) < 128 - k.val) := by
        intro v row2 hrow2 hm hv127
        have htr := hwrite v row2 hrow2 hm hv127
        exact ⟨by omega, htr.1, htr.2.1, htr.2.2, by omega⟩
      split
      · rename_i hn
        step with Array.update_spec row1 k (-127)#i64 (by simp; omega) as ⟨row2, hrow2⟩
        step as ⟨k1, hk1'⟩
        have hk1v : k1.val = k.val + 1 := by scalar_tac
        simp only [hk1v]
        have hl : s.val < (-127 : Int) := hn
        have hm : GeneralModel.clampEntry mrow[k.val]! = ((-127)#i64).val := by
          rw [hentry, ← clamp_entry_spec, ← hsval, ite_eq_left hl]
          rfl
        apply hfinish (-127)#i64 row2 hrow2 hm
        change (-127 : Int) ≤ -127 ∧ (-127 : Int) ≤ 127
        omega
      · rename_i hn1
        have hl : ¬ s.val < (-127 : Int) := hn1
        split
        · rename_i hn2
          step with Array.update_spec row1 k 127#i64 (by simp; omega) as ⟨row2, hrow2⟩
          step as ⟨k1, hk1'⟩
          have hk1v : k1.val = k.val + 1 := by scalar_tac
          simp only [hk1v]
          have hu : (127 : Int) < s.val := hn2
          have hm : GeneralModel.clampEntry mrow[k.val]! = (127#i64).val := by
            rw [hentry, ← clamp_entry_spec, ← hsval, ite_eq_right hl, ite_eq_left hu]
            rfl
          apply hfinish 127#i64 row2 hrow2 hm
          change (-127 : Int) ≤ 127 ∧ (127 : Int) ≤ 127
          omega
        · rename_i hn2
          step with Array.update_spec row1 k s (by simp; omega) as ⟨row2, hrow2⟩
          step as ⟨k1, hk1'⟩
          have hk1v : k1.val = k.val + 1 := by scalar_tac
          simp only [hk1v]
          have hu : ¬ (127 : Int) < s.val := hn2
          have hm : GeneralModel.clampEntry mrow[k.val]! = s.val := by
            rw [hentry, ← clamp_entry_spec, ← hsval, ite_eq_right hl, ite_eq_right hu]
          exact hfinish s row2 hrow2 hm (by omega)
    · have hk128 : k.val = 128 := by scalar_tac
      simp only [WP.spec_ok]
      change ints row1 = mrow.map GeneralModel.clampEntry ∧ Bounded Envelope.embedding row1
      refine ⟨?_, hbd⟩
      apply List.ext_getElem
      · simp only [List.length_map, hmrow_len, ints_length128]
      · intro q hq1 hq2
        rw [ints_length128] at hq1
        have hq : q < 128 := by omega
        have hrowq : (ints row1)[q]'(by rw [ints_length128]; omega) =
            GeneralModel.clampEntry mrow[q]! :=
          heq q hq (by rw [hk128]; omega)
        rw [hrowq, List.getElem_map, getElem!_pos mrow q (by rw [hmrow_len]; exact hq)]
  · simp only
    refine ⟨by scalar_tac, ?_, ?_, ?_⟩
    · intro q hq hiq
      exact absurd hiq (Nat.not_lt.mpr (Nat.zero_le q))
    · intro q hq hiq
      have hz : ∀ x ∈ (Array.repeat 128#usize 0#i64).val, x = 0#i64 := by
        intro x hx
        rw [repeat_val_probe] at hx
        exact (List.mem_replicate.mp hx).2
      exact hz _ (List.getElem_mem _)
    · intro v hv
      rw [repeat_val_probe] at hv
      rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
      constructor <;> simp only [Envelope.embedding] <;> norm_num

end LcnExec.GeneralEngine
