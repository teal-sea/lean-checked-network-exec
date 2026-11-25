import LcnExec.GeneralEngine.AttentionAt

/-!
# Residual: the scaled token stream plus attention output
-/

open Aeneas Aeneas.Std Result ControlFlow

set_option maxHeartbeats 800000

namespace LcnExec.GeneralEngine

theorem residual_length (xs bs : List Int) (h : xs.length = bs.length) :
    (GeneralModel.residual xs bs).length = xs.length := by
  induction xs generalizing bs with
  | nil => cases bs with
    | nil => rfl
    | cons a bs' => exact absurd h (by simp)
  | cons x xs' ih =>
    cases bs with
    | nil => exact absurd h.symm (by simp)
    | cons a bs' => simpa [GeneralModel.residual] using ih bs' (by simpa using h)

theorem residual_getElem : ∀ (xs bs : List Int) (i : Nat),
    i < xs.length → i < bs.length → xs.length = bs.length →
    (GeneralModel.residual xs bs)[i]! = xs[i]! * GeneralModel.ALPHA_ONE + bs[i]!
  | [], _, i, hx, _, _ => by simp at hx
  | x :: xs', [], i, _, ha, _ => by simp at ha
  | x :: xs', b :: bs', 0, _, _, _ => by simp [GeneralModel.residual]
  | x :: xs', b :: bs', i' + 1, hx, ha, hlen => by
      simp only [List.length_cons] at hx ha hlen ⊢
      have hrec := residual_getElem xs' bs' i' (by omega) (by omega) (by omega)
      simp only [GeneralModel.residual]
      simpa using hrec

theorem residual_mul_bounds_probe (i : I64)
    (h : -Envelope.embedding <= i.val ∧ i.val <= Envelope.embedding) :
    I64.min <= i.val * (16777216#i64).val ∧ i.val * (16777216#i64).val <= I64.max := by
  change -127 <= i.val ∧ i.val <= 127 at h
  have hprod : -2130706432 <= i.val * (16777216#i64).val ∧
      i.val * (16777216#i64).val <= 2130706432 := by
    change -2130706432 <= i.val * 16777216 ∧ i.val * 16777216 <= 2130706432
    omega
  constructor <;> scalar_tac

theorem residual_getElem_plain_probe (xs bs : List Int) (i : Nat) (hx : i < xs.length)
    (hb : i < bs.length) (hs : xs.length = bs.length)
    (hm : i < (GeneralModel.residual xs bs).length) :
    (GeneralModel.residual xs bs)[i]'hm = xs[i]'hx * GeneralModel.ALPHA_ONE + bs[i]'hb := by
  have h := residual_getElem xs bs i hx hb hs
  rw [getElem!_pos (GeneralModel.residual xs bs) i hm,
    getElem!_pos xs i hx, getElem!_pos bs i hb] at h
  exact h

theorem residual_zero_bounds_probe : -Envelope.residual ≤ (0#i64).val ∧
    (0#i64).val ≤ Envelope.residual := by
  change (-5253256708096 : Int) ≤ 0 ∧ (0 : Int) ≤ 5253256708096
  norm_num

theorem residual_spec (x att : Array I64 128#usize)
    (hx : Bounded Envelope.embedding x) (hatt : Bounded Envelope.attention att) :
    general_engine.residual x att ⦃ r =>
      ints r = GeneralModel.residual (ints x) (ints att) ∧
      Bounded Envelope.residual r ⦄ := by
  have halpha : general_engine.ALPHA_ONE = ok 16777216#i64 := by
    unfold general_engine.ALPHA_ONE; rfl
  unfold general_engine.residual general_engine.residual_loop
  apply loop.spec_decr_nat
    (measure := fun (st : Array I64 128#usize × Usize) => 128 - st.2.val)
    (inv := fun (st : Array I64 128#usize × Usize) =>
      st.2.val ≤ 128 ∧
      Bounded Envelope.residual st.1 ∧
      (∀ (k : Nat) (hk : k < 128) (hik : k < st.2.val),
        (ints st.1)[k]'(by rw [ints_length128]; omega) =
          (ints x)[k]'(by rw [ints_length128]; omega) * GeneralModel.ALPHA_ONE +
            (ints att)[k]'(by rw [ints_length128]; omega)) ∧
      (∀ (k : Nat) (hk : k < 128) (hik : ¬ k < st.2.val),
        st.1.val[k]'(by simp; omega) = (Array.repeat 128#usize 0#i64).val[k]'(by simp; omega)))
  · rintro ⟨r1, k⟩ ⟨hk1, hbd, heq, hsuf⟩
    unfold general_engine.residual_loop.body
    dsimp only at hk1 hbd heq hsuf ⊢
    simp only [general_engine.D_MODEL]
    split
    · have hk128 : k.val < 128 := by scalar_tac
      step with Array.index_usize_spec x k (by simp; omega) as ⟨i, hiv⟩
      have hivb : -Envelope.embedding ≤ i.val ∧ i.val ≤ Envelope.embedding := by
        have hmem : x.val[k.val]'(by simp; omega) ∈ x.val :=
          List.getElem_mem (by simp; omega)
        have hbound := hx _ hmem
        rw [← hiv] at hbound
        exact hbound
      rw [halpha]
      have hmul := residual_mul_bounds_probe i hivb
      step with I64.mul_spec hmul.1 hmul.2 as ⟨i2, hi2⟩
      step with Array.index_usize_spec att k (by simp; omega) as ⟨i3, hi3v⟩
      have hattb : -Envelope.attention ≤ i3.val ∧ i3.val ≤ Envelope.attention := by
        have hmem : att.val[k.val]'(by simp; omega) ∈ att.val :=
          List.getElem_mem (by simp; omega)
        have hbound := hatt _ hmem
        rw [← hi3v] at hbound
        exact hbound
      have hnum : 2130706432 + Envelope.attention ≤ Envelope.residual := by
        simp only [Envelope.attention, Envelope.residual]
        norm_num
      have hpb : -2130706432 ≤ i2.val ∧ i2.val ≤ 2130706432 := by
        have hiv127 : -127 ≤ i.val ∧ i.val ≤ 127 := hivb
        have hprod : -2130706432 ≤ i.val * 16777216 ∧ i.val * 16777216 ≤ 2130706432 := by
          omega
        rw [hi2]
        exact hprod
      have hmina : I64.min ≤ i2.val + i3.val := by
        change -5251126001664 ≤ i3.val ∧ i3.val ≤ 5251126001664 at hattb
        have hbb := hpb
        scalar_tac
      have hmaxa : i2.val + i3.val ≤ I64.max := by
        change -5251126001664 ≤ i3.val ∧ i3.val ≤ 5251126001664 at hattb
        have hbb := hpb
        scalar_tac
      step with I64.add_spec hmina hmaxa as ⟨i4, hi4⟩
      step with Array.update_spec r1 k i4 (by simp; omega) as ⟨a, ha⟩
      step as ⟨k1, hk1'⟩
      have hkv : k1.val = k.val + 1 := by scalar_tac
      simp only [hkv]
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · rw [ha]
        exact project_bounded_set _ _ _ _ hbd ⟨by rw [hi4]; omega, by rw [hi4]; omega⟩
      · intro k' hk' hik
        by_cases hkk : k' = k.val
        · subst k'
          have hset : (ints a)[k.val]'(by rw [ints_length128]; omega) = i4.val := by
            rw [ha]
            simp only [ints, Array.set_val_eq, List.getElem_map]
            rw [List.getElem_set_self (by simp; omega)]
          have hxv : (ints x)[k.val]'(by rw [ints_length128]; omega) = i.val := by
            simp only [ints, List.getElem_map]
            rw [hiv]
          have hattv : (ints att)[k.val]'(by rw [ints_length128]; omega) = i3.val := by
            simp only [ints, List.getElem_map]
            rw [hi3v]
          rw [hset, hxv, hattv, hi4, hi2]
          rfl
        · have hval : (ints a)[k']'(by rw [ints_length128]; omega) =
              (ints r1)[k']'(by rw [ints_length128]; omega) := by
            rw [ha]
            simp only [ints, Array.set_val_eq, List.getElem_map]
            rw [List.getElem_set_ne (by omega)]
          rw [hval]
          exact heq k' hk' (by omega)
      · intro k' hk' hik
        have hval : a.val[k']'(by simp; omega) = r1.val[k']'(by simp; omega) := by
          rw [ha]
          simp only [Array.set_val_eq]
          rw [List.getElem_set_ne (by omega)]
        rw [hval]
        exact hsuf k' hk' (by omega)
    · have hk128 : k.val = 128 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, hbd⟩
      apply List.ext_getElem
      · simp [ints_length128, residual_length]
      · intro k' hk' hk''
        have hk'128 : k' < 128 := by rw [ints_length128] at hk'; omega
        have hmod := residual_getElem_plain_probe (ints x) (ints att) k'
          (by rw [ints_length128]; omega) (by rw [ints_length128]; omega)
          (by simp [ints_length128]) hk''
        exact (heq k' hk'128 (by omega)).trans hmod.symm
  · simp only
    refine ⟨by scalar_tac, ?_, ?_, ?_⟩
    · intro v hv
      rcases List.mem_replicate.mp (show v ∈ List.replicate 128 0#i64 from by
        simpa [Array.repeat] using hv) with ⟨-, rfl⟩
      exact residual_zero_bounds_probe
    · intro k' hk' hik
      exact absurd hik (by show ¬(k' < 0); omega)
    · intro k' hk' hik
      simp only

end LcnExec.GeneralEngine
