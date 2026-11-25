import LcnExec.GeneralEngine.MlpOutputInner

set_option maxHeartbeats 800000

open Aeneas Aeneas.Std Result ControlFlow

namespace LcnExec.GeneralEngine

/-- Column `v` of the output matrix, with one signed weight per input coordinate. -/
def unembedColumn (W : general_engine.Weights) (v : Nat) : List Int :=
  W.u.val.map (fun row => (row.val[v]!).val)

theorem unembedColumn_length (W : general_engine.Weights) (v : Nat) :
    (unembedColumn W v).length = 128 := by
  simp [unembedColumn]

/-- The generated dot starts at zero and accumulates at most
`128 * 124539743797248 * 37 = 589820226623766528` in magnitude. -/
theorem unembed_inner_spec (W : general_engine.Weights) (hW : LoadBounds W)
    (fin : Array I64 128#usize) (hfin : Bounded Envelope.final_stream fin)
    (v : Usize) (hv : v.val < 256) :
    general_engine.unembed_loop0_loop0 W fin v 0#i64 0#usize ⦃ r =>
      r.1 = W ∧
      r.2.val = GeneralModel.dot (ints fin) (unembedColumn W v.val) ∧
      -Envelope.logit ≤ r.2.val ∧ r.2.val ≤ Envelope.logit ⦄ := by
  unfold general_engine.unembed_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (st : I64 × Usize) => 128 - st.2.val)
    (inv := fun (st : I64 × Usize) =>
      st.2.val ≤ 128 ∧
      st.1.val + GeneralModel.dot ((ints fin).drop st.2.val)
          ((unembedColumn W v.val).drop st.2.val) =
        GeneralModel.dot (ints fin) (unembedColumn W v.val) ∧
      -4607970520498176 * (st.2.val : Int) ≤ st.1.val ∧
      st.1.val ≤ 4607970520498176 * (st.2.val : Int))
  · rintro ⟨acc, k⟩ ⟨hk1, hacc, hlo, hhi⟩
    unfold general_engine.unembed_loop0_loop0.body
    dsimp only at hk1 hacc hlo hhi ⊢
    simp only [general_engine.D_MODEL]
    split
    · have hk : k.val < 128 := by scalar_tac
      rw [dot_drop _ _ _ (by rwa [ints_length128]) (by rwa [unembedColumn_length])] at hacc
      step as ⟨x, hx⟩
      step as ⟨row, hrow⟩
      step as ⟨weight, hweight⟩
      step as ⟨wide, hwide⟩
      have hcast : wide.val = weight.val := by scalar_tac
      have hxmem : x ∈ fin.val := by
        rw [hx]
        exact List.getElem_mem _
      have hrowmem : row ∈ W.u.val := by
        rw [hrow]
        exact List.getElem_mem _
      have hwmem : weight ∈ row.val := by
        rw [hweight]
        exact List.getElem_mem _
      have hwb : -(37 : Int) ≤ wide.val ∧ wide.val ≤ 37 := by
        rw [hcast]
        exact hW.u row hrowmem weight hwmem
      have hxb := hfin x hxmem
      have hprod : -4607970520498176 ≤ x.val * wide.val ∧
          x.val * wide.val ≤ 4607970520498176 := by
        have hcap : Envelope.final_stream * (37 : Int) = 4607970520498176 := by
          norm_num [Envelope.final_stream]
        have hbound := project_mul_bound x.val wide.val Envelope.final_stream 37
          (by norm_num [Envelope.final_stream]) (by norm_num) hxb hwb
        rw [hcap] at hbound
        exact hbound
      have hmulmin : I64.min ≤ x.val * wide.val := by
        have h := hprod.1
        scalar_tac
      have hmulmax : x.val * wide.val ≤ I64.max := by
        have h := hprod.2
        scalar_tac
      step with I64.mul_spec hmulmin hmulmax as ⟨prod, hprodval⟩
      have hprodval' : prod.val = x.val * wide.val := by scalar_tac
      have hprodlo : -4607970520498176 ≤ prod.val := by
        rw [hprodval']
        exact hprod.1
      have hprodhi : prod.val ≤ 4607970520498176 := by
        rw [hprodval']
        exact hprod.2
      have hnextlo : -4607970520498176 * ((k.val : Int) + 1) ≤ acc.val + prod.val := by
        omega
      have hnexthi : acc.val + prod.val ≤ 4607970520498176 * ((k.val : Int) + 1) := by
        omega
      have haddmin : I64.min ≤ acc.val + prod.val := by
        have h : -589820226623766528 ≤ acc.val + prod.val := by omega
        scalar_tac
      have haddmax : acc.val + prod.val ≤ I64.max := by
        have h : acc.val + prod.val ≤ 589820226623766528 := by omega
        scalar_tac
      step with I64.add_spec haddmin haddmax as ⟨acc1, hacc1⟩
      step as ⟨k1, hk1'⟩
      have hk1v : k1.val = k.val + 1 := by scalar_tac
      have hacc1v : acc1.val = acc.val + prod.val := by scalar_tac
      have hxi : (ints fin)[k.val]'(by rwa [ints_length128]) = x.val := by
        simp only [ints, List.getElem_map]
        rw [hx]
      have hwi : (unembedColumn W v.val)[k.val]'(by rwa [unembedColumn_length]) = wide.val := by
        simp only [unembedColumn, List.getElem_map]
        rw [← hrow, getElem!_pos row.val v.val (by rwa [Array.length_eq]), ← hweight, hcast]
      rw [hxi, hwi] at hacc
      simp only [hk1v]
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · exact mlp_tail_linear_probe acc.val x.val wide.val acc1.val prod.val
          (GeneralModel.dot ((ints fin).drop (k.val + 1))
            ((unembedColumn W v.val).drop (k.val + 1)))
          (GeneralModel.dot (ints fin) (unembedColumn W v.val)) hacc hprodval' hacc1v
      · rw [hacc1v]
        omega
      · rw [hacc1v]
        omega
    · have hk128 : k.val = 128 := by scalar_tac
      simp only [WP.spec_ok]
      rw [hk128] at hacc
      have hzFin : (ints fin).drop 128 = [] := by simp [ints_length128]
      have hzCol : (unembedColumn W v.val).drop 128 = [] := by simp [unembedColumn_length]
      rw [hzFin, hzCol] at hacc
      have hdot : acc.val = GeneralModel.dot (ints fin) (unembedColumn W v.val) := by
        simpa [GeneralModel.dot] using hacc
      refine ⟨trivial, hdot, ?_, ?_⟩
      · simp only [Envelope.logit]
        omega
      · simp only [Envelope.logit]
        omega
  · simp only
    refine ⟨by scalar_tac, ?_, ?_, ?_⟩
    · show (0 : Int) + GeneralModel.dot (ints fin) (unembedColumn W v.val) =
        GeneralModel.dot (ints fin) (unembedColumn W v.val)
      exact Int.zero_add _
    · change (-4607970520498176 : Int) * 0 ≤ 0
      norm_num
    · change (0 : Int) ≤ 4607970520498176 * 0
      norm_num

end LcnExec.GeneralEngine
