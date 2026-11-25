import LcnExec.GeneralEngine.ValueScan

/-!
# The inner weighted-sum loop of `general_engine.head_out_at`

`head_out_at_loop1_loop0` folds `acc += alpha[jj] * vs[jj][i]` over `jj <= p`.
Exact signed fold equality (pre-shift) with a checked-arithmetic envelope
`|acc| <= Envelope.value * sum(take jj (ints alpha))` for nonnegative alphas.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace LcnExec.GeneralEngine

theorem take_sum_succ {l : List Int} {n : Nat} (hn : n + 1 ≤ l.length) :
    (l.take (n + 1)).sum = (l.take n).sum + l[n]'(by omega) := by
  have hget : l[n]? = some (l[n]'(by omega)) := List.getElem?_eq_getElem (by omega)
  rw [List.take_add_one, hget, Option.toList_some,
    List.sum_append, List.sum_cons, List.sum_nil, Int.add_zero]

/-- Checked accumulator update: if `|acc| <= B*s` and `|v| <= B`, `a >= 0`, then
`|acc + a*v| <= B*(s+a)`, by explicit `mul_le_mul_of_nonneg_left` and `ring`. -/
theorem acc_update_bound {B s a v acc : Int}
    (ha : 0 ≤ a) (hv : -B ≤ v) (hv2 : v ≤ B)
    (hlo : -(B * s) ≤ acc) (hhi : acc ≤ B * s) :
    -(B * (s + a)) ≤ acc + a * v ∧ acc + a * v ≤ B * (s + a) := by
  have hupper : a * v ≤ B * a := by
    have h1 : a * v ≤ a * B := mul_le_mul_of_nonneg_left hv2 ha
    rw [mul_comm B a]
    exact h1
  have hlower : -(B * a) ≤ a * v := by
    have h1 : a * (-B) ≤ a * v := mul_le_mul_of_nonneg_left hv ha
    have h2 : -(B * a) = a * (-B) := by ring
    rw [h2]; exact h1
  constructor
  · have e : B * (s + a) = B * s + B * a := by ring
    rw [e]
    linarith
  · have e : B * (s + a) = B * s + B * a := by ring
    rw [e]
    linarith

theorem head_out_mix_inner_spec (p : Usize) (hp : p.val < 32)
    (alpha : Array I64 32#usize) (vs : Array (Array I64 32#usize) 32#usize) (i : Usize)
    (hi : i.val < 32)
    (halpha : ∀ j (_ : j ≤ p.val), 0 ≤ (ints alpha)[j]'(by rw [ints_length32]; omega))
    (hsum : ((ints alpha).take (p.val + 1)).sum ≤ 16777216)
    (hvs : ∀ row ∈ vs.val, Bounded Envelope.value row) :
    general_engine.head_out_at_loop1_loop0 p alpha vs i 0#i64 0#usize ⦃ r =>
      r.val = (List.range (p.val + 1)).foldl
        (fun acc j => acc + GeneralModel.nth 0 (ints alpha) j *
          GeneralModel.nth 0 (GeneralModel.rowAt (vals2 vs) j) i.val) 0 ⦄ := by
  have hvval : 0 ≤ Envelope.value := by simp only [Envelope.value]; norm_num
  unfold general_engine.head_out_at_loop1_loop0
  apply loop.spec_decr_nat
    (measure := fun (st : I64 × Usize) => p.val + 1 - st.2.val)
    (inv := fun (st : I64 × Usize) =>
      st.2.val ≤ p.val + 1 ∧
      st.1.val = (List.range st.2.val).foldl
        (fun acc j => acc + GeneralModel.nth 0 (ints alpha) j *
          GeneralModel.nth 0 (GeneralModel.rowAt (vals2 vs) j) i.val) 0 ∧
      -(Envelope.value * ((ints alpha).take st.2.val).sum) ≤ st.1.val ∧
      st.1.val ≤ Envelope.value * ((ints alpha).take st.2.val).sum)
  · rintro ⟨acc, jj⟩ ⟨hjj1, hfold, hlo, hhi⟩
    unfold general_engine.head_out_at_loop1_loop0.body
    dsimp only at hjj1 hfold hlo hhi ⊢
    split
    · have hjp : jj.val ≤ p.val := by scalar_tac
      have hjj32 : jj.val < 32 := by omega
      step as ⟨i1, hi1⟩
      step as ⟨a, ha⟩
      step as ⟨i2, hi2⟩
      have hali1 : i1.val = (ints alpha)[jj.val]'(by rw [ints_length32]; omega) := by
        simp [ints, hi1]
      have hrow : (vals2 vs)[jj.val]'(by rw [vals2_length]; omega) = ints a := by
        simp only [vals2, List.getElem_map, ha]
      have hli : i.val < (ints a).length := by rw [ints_length32]; omega
      have hi2v : (ints a)[i.val]'hli = i2.val := by
        simp [ints, hi2]
      have hib : -Envelope.value ≤ i2.val ∧ i2.val ≤ Envelope.value := by
        have hmem : a ∈ vs.val := by rw [ha]; exact List.getElem_mem (by simp; omega)
        have hb := hvs a hmem
        exact hb i2 (by simp [hi2])
      have hi1nn : 0 ≤ i1.val := by rw [hali1]; exact halpha jj.val hjp
      have htake1 : ((ints alpha).take (p.val + 1)).length = p.val + 1 := by
        rw [List.length_take, ints_length32]
        omega
      have hl2 : jj.val < (ints alpha).length := by rw [ints_length32]; omega
      have hmemtake : (ints alpha)[jj.val]'hl2
          ∈ (ints alpha).take (p.val + 1) := by
        have hl1 : jj.val < ((ints alpha).take (p.val + 1)).length := by
          rw [htake1]; omega
        have ht : ((ints alpha).take (p.val + 1))[jj.val]'hl1 =
            (ints alpha)[jj.val]'hl2 :=
          (List.getElem_take' hl2 (by omega)).symm
        rw [← ht]
        exact List.getElem_mem hl1
      have hpnn : ∀ x ∈ (ints alpha).take (p.val + 1), 0 ≤ x := by
        intro x hx
        rcases List.mem_iff_getElem.mp hx with ⟨j0, hj0, hje⟩
        have h1 := hj0
        rw [List.length_take] at h1
        have hj0lt : j0 < p.val + 1 := by omega
        have hl3 : j0 < (ints alpha).length := by rw [ints_length32]; omega
        have ht0 : ((ints alpha).take (p.val + 1))[j0]'hj0 =
            (ints alpha)[j0]'hl3 :=
          (List.getElem_take' hl3 hj0lt).symm
        rw [← hje, ht0]
        exact halpha j0 (by omega)
      have hi1dom : i1.val ≤ ((ints alpha).take (p.val + 1)).sum := by
        rw [hali1]
        exact list_sum_ge_mem _ hpnn _ hmemtake
      have hi1le : i1.val ≤ 16777216 := le_trans hi1dom hsum
      have hvv : Envelope.value = 1723136 := by simp only [Envelope.value]
      have hib2 : -1723136 ≤ i2.val ∧ i2.val ≤ 1723136 := hib
      have hi1l2 : i1.val ≤ 16777216 := hi1le
      have hprod : -(16777216 * 1723136) ≤ i1.val * i2.val ∧
          i1.val * i2.val ≤ 16777216 * 1723136 := by
        constructor <;> nlinarith [mul_nonneg (by omega : 0 ≤ i1.val)
          (by omega : 0 ≤ i2.val + 1723136),
          mul_nonneg (by omega : 0 ≤ i1.val) (by omega : 0 ≤ 1723136 - i2.val)]
      have hminb : I64.min ≤ i1.val * i2.val := by scalar_tac
      have hmaxb : i1.val * i2.val ≤ I64.max := by scalar_tac
      step with I64.mul_spec hminb hmaxb as ⟨i3, hi3⟩
      have hSjj : ((ints alpha).take jj.val).sum ≤ ((ints alpha).take (p.val + 1)).sum := by
        have h1 := List.take_append_drop jj.val ((ints alpha).take (p.val + 1))
        have h2 : ((ints alpha).take (p.val + 1)).take jj.val =
            (ints alpha).take jj.val := by
          rw [List.take_take]
          congr 1
          omega
        rw [h2] at h1
        rw [← h1, List.sum_append]
        have hdnn : 0 ≤ (((ints alpha).take (p.val + 1)).drop jj.val).sum := by
          refine list_sum_nonneg _ ?_
          intro x hx
          have hx2 : x ∈ (ints alpha).take (p.val + 1) := List.mem_of_mem_drop hx
          exact hpnn x hx2
        omega
      have hP : Envelope.value * ((ints alpha).take jj.val).sum ≤ 28909424869376 := by
        rw [hvv]; nlinarith
      have hPneg : -28909424869376 ≤ Envelope.value * ((ints alpha).take jj.val).sum := by
        rw [hvv]; nlinarith
      step as ⟨acc1, hacc1⟩
      step as ⟨jj1, hjj1'⟩
      have hsumup : ((ints alpha).take (jj.val + 1)).sum =
          ((ints alpha).take jj.val).sum +
          (ints alpha)[jj.val]'(by rw [ints_length32]; omega) :=
        take_sum_succ (by rw [ints_length32]; omega)
      have hn1 : GeneralModel.nth 0 (ints alpha) jj.val =
          (ints alpha)[jj.val]'(by rw [ints_length32]; omega) :=
        project_nth_eq _ _ _ (by rw [ints_length32]; omega)
      have hnr : GeneralModel.rowAt (vals2 vs) jj.val =
          (vals2 vs)[jj.val]'(by rw [vals2_length]; omega) := by
        rw [GeneralModel.rowAt, project_nth_eq _ _ _ (by rw [vals2_length]; omega)]
      have hn2 : GeneralModel.nth 0 (GeneralModel.rowAt (vals2 vs) jj.val) i.val = i2.val :=
        (congrArg (fun row => GeneralModel.nth 0 row i.val) (hnr.trans hrow)).trans
          ((project_nth_eq 0 (ints a) i.val hli).trans hi2v)
      have hfoldstep : (List.range (jj.val + 1)).foldl
          (fun acc j => acc + GeneralModel.nth 0 (ints alpha) j *
            GeneralModel.nth 0 (GeneralModel.rowAt (vals2 vs) j) i.val) 0
          = (List.range jj.val).foldl
            (fun acc j => acc + GeneralModel.nth 0 (ints alpha) j *
              GeneralModel.nth 0 (GeneralModel.rowAt (vals2 vs) j) i.val) 0
            + (GeneralModel.nth 0 (ints alpha) jj.val *
              GeneralModel.nth 0 (GeneralModel.rowAt (vals2 vs) jj.val) i.val) := by
        rw [List.range_succ, List.foldl_append]
        simp
      simp only [hjj1']
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · rw [hfoldstep, hacc1, hi3, hfold, hn1, hali1, hn2]
      · have hb := acc_update_bound (B := Envelope.value)
          (s := ((ints alpha).take jj.val).sum) (a := i1.val) (v := i2.val)
          (acc := acc.val) hi1nn hib.1 hib.2 hlo hhi
        rw [hacc1, hi3, hsumup, ← hali1]
        exact hb.1
      · have hb := acc_update_bound (B := Envelope.value)
          (s := ((ints alpha).take jj.val).sum) (a := i1.val) (v := i2.val)
          (acc := acc.val) hi1nn hib.1 hib.2 hlo hhi
        rw [hacc1, hi3, hsumup, ← hali1]
        exact hb.2
    · have hjp : jj.val = p.val + 1 := by scalar_tac
      simp only [WP.spec_ok]
      rw [hjp] at hfold
      exact hfold
  · simp only
    refine ⟨by scalar_tac, ?_, ?_, ?_⟩
    · simp
    · -- trace_state is load-bearing here: it forces instantiation of the invariant's
      -- metavariable proofs so that `simp [hz]` can match the take-0 goal.
      trace_state
      have hz : (0#usize).val = 0 := by decide
      constructor <;> simp [hz]
    · trace_state
      have hz : (0#usize).val = 0 := by decide
      constructor <;> simp [hz]

end LcnExec.GeneralEngine
