import LcnExec.GeneralEngine.RescaleInner

set_option maxHeartbeats 800000

open Aeneas Aeneas.Std Result ControlFlow

namespace LcnExec.GeneralEngine

theorem rescale_clamp_loop0_spec (f : Array (Array I64 128#usize) 32#usize)
    (hfb : ∀ row ∈ f.val, Bounded Envelope.final_stream row) :
    general_engine.rescale_clamp_loop0 f
        (Array.repeat 32#usize (Array.repeat 128#usize 0#i64)) 0#usize ⦃ out =>
      ints2 out = GeneralModel.rescaleClamp (ints2 f) ∧ streams out ⦄ := by
  unfold general_engine.rescale_clamp_loop0
  apply loop.spec_decr_nat
    (measure := fun (st : Array (Array I64 128#usize) 32#usize × Usize) =>
      32 - st.2.val)
    (inv := fun (st : Array (Array I64 128#usize) 32#usize × Usize) =>
      st.2.val ≤ 32 ∧
      (∀ (q : Nat) (hq : q < 32) (hiq : q < st.2.val),
        (ints2 st.1)[q]'(by rw [ints2_length]; exact hq) =
          ((ints2 f)[q]!).map GeneralModel.clampEntry) ∧
      (∀ (q : Nat) (hq : q < 32) (hiq : st.2.val ≤ q),
        st.1.val[q]'(by simpa using hq) = Array.repeat 128#usize 0#i64) ∧
      (∀ row ∈ st.1.val, Bounded Envelope.embedding row))
  · rintro ⟨out, p⟩ ⟨hp1, heq, hsuf, hbd⟩
    unfold general_engine.rescale_clamp_loop0.body
    dsimp only at hp1 heq hsuf hbd ⊢
    simp only [general_engine.MAX_SEQ]
    split
    · have hp : p.val < 32 := by scalar_tac
      step with rescale_clamp_inner_spec f hfb p hp as ⟨r, hreq, hrbound⟩
      step with Array.update_spec out p r (by simpa using hp) as ⟨a, ha⟩
      step as ⟨p1, hp1'⟩
      have hp1v : p1.val = p.val + 1 := by scalar_tac
      simp only [hp1v]
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · intro q hq hiq
        by_cases hqq : q = p.val
        · subst q
          have hset : (ints2 a)[p.val]'(by rw [ints2_length]; exact hp) = ints r := by
            rw [ha]
            simp only [ints2, Array.set_val_eq, List.getElem_map]
            rw [List.getElem_set_self (by simp; omega)]
          rw [hset, hreq]
        · have hval : (ints2 a)[q]'(by rw [ints2_length]; exact hq) =
              (ints2 out)[q]'(by rw [ints2_length]; exact hq) := by
            rw [ha]
            simp only [ints2, Array.set_val_eq, List.getElem_map]
            rw [List.getElem_set_ne (by omega)]
          rw [hval]
          exact heq q hq (by omega)
      · intro q hq hiq
        have hval : a.val[q]'(by simpa using hq) = out.val[q]'(by simpa using hq) := by
          subst ha
          simp only [Array.set_val_eq]
          rw [List.getElem_set_ne (by omega)]
        rw [hval]
        exact hsuf q hq (by omega)
      · intro row hrow
        rw [ha, Array.set_val_eq out p r] at hrow
        rcases List.mem_or_eq_of_mem_set hrow with h | h
        · exact hbd row h
        · rw [h]
          exact hrbound
    · have hpdone : p.val = 32 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, hbd⟩
      apply List.ext_getElem
      · simp only [GeneralModel.rescaleClamp, List.length_map, ints2_length]
      · intro q hq1 hq2
        have hq : q < 32 := by simpa only [ints2_length] using hq1
        have hqf : q < (ints2 f).length := by rwa [ints2_length]
        simpa only [GeneralModel.rescaleClamp, List.getElem_map,
          getElem!_pos (ints2 f) q hqf] using heq q hq (by omega)
  · simp only
    refine ⟨by scalar_tac, ?_, ?_, ?_⟩
    · intro q hq hiq
      exact absurd hiq (Nat.not_lt.mpr (Nat.zero_le q))
    · intro q hq hiq
      show (List.replicate 32 (Array.repeat 128#usize 0#i64))[q]'(by simp; omega) =
        Array.repeat 128#usize 0#i64
      exact List.getElem_replicate hq
    · intro row hrow
      have hm : List.Mem row (List.replicate 32 (Array.repeat 128#usize 0#i64)) := hrow
      have hzero : row = Array.repeat 128#usize 0#i64 := (List.mem_replicate.mp hm).2
      rw [hzero]
      intro v hv
      rw [repeat_val_probe] at hv
      have hvzero : v = 0#i64 := (List.mem_replicate.mp hv).2
      rw [hvzero]
      constructor <;> simp only [Envelope.embedding] <;> norm_num

theorem rescale_clamp_spec (f : Array (Array I64 128#usize) 32#usize)
    (hfb : ∀ row ∈ f.val, Bounded Envelope.final_stream row) :
    general_engine.rescale_clamp f ⦃ out =>
      ints2 out = GeneralModel.rescaleClamp (ints2 f) ∧ streams out ⦄ := by
  unfold general_engine.rescale_clamp
  exact rescale_clamp_loop0_spec f hfb

end LcnExec.GeneralEngine
