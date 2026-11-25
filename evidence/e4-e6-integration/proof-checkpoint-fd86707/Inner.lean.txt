import LcnExec.GeneralEngine.MlpHidden

set_option maxHeartbeats 800000

/-!
# The MLP output inner dot loop `general_engine.mlp_output_loop0_loop0`

`acc = sum_i m[i] * wout[i][k]` over `i < 512` (the `wout` column at `k < 128`),
with the input weights returned unchanged. Exact `GeneralModel.dot` and the
two-sided pure-dot cap `512 * 215384598773760 * 74 = 8160491678340218880`.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace LcnExec.GeneralEngine

/-- The `wout` column for output coordinate `k`: entries `wout[i][k]`. -/
def woutColumn (w : general_engine.Weights) (l k : Nat) : List Int :=
  ((w.layers.val[l]!).wout.val).map (fun row => (row.val[k]!).val)

theorem woutColumn_length (w : general_engine.Weights) (l k : Nat) :
    (woutColumn w l k).length = 512 := by
  simp [woutColumn]

theorem wout_column_entry_probe (W : general_engine.Weights) (l t k : Usize)
    (ht : t.val < 512) (hk : k.val < 128)
    (a : Array I8 128#usize) (iv : I8) (casted : I64)
    (hrow : (W.layers.val[l.val]!).wout.val[t.val]! = a)
    (hentry : iv = a.val[k.val]'(by rw [Array.length_eq]; exact hk))
    (hcast : casted.val = iv.val) :
    (woutColumn W l.val k.val)[t.val]'(by rw [woutColumn_length]; exact ht) = casted.val := by
  have ht' : t.val < (W.layers.val[l.val]!).wout.val.length := by
    rw [Array.length_eq]; exact ht
  rw [getElem!_pos (W.layers.val[l.val]!).wout.val t.val ht'] at hrow
  simp only [woutColumn, List.getElem_map]
  rw [hrow, getElem!_pos a.val k.val (by rw [Array.length_eq]; exact hk), ← hentry, hcast]

theorem mlp_output_inner_spec (W : general_engine.Weights) (hW : LoadBounds W)
    (l : Usize) (hl : l.val < 2)
    (m : Array I64 512#usize) (hm : Bounded Envelope.hidden m)
    (k : Usize) (hk : k.val < 128) :
    general_engine.mlp_output_loop0_loop0 W l m k 0#i64 0#usize ⦃ r =>
      r.1 = W ∧
      r.2.val = GeneralModel.dot (ints m) (woutColumn W l.val k.val) ∧
      -8160491678340218880 ≤ r.2.val ∧ r.2.val ≤ 8160491678340218880 ⦄ := by
  have hL := layerBounds hW l hl
  have hrc : ∀ x ∈ (ints m), -Envelope.hidden ≤ x ∧ x ≤ Envelope.hidden := by
    intro x hx
    change x ∈ m.val.map (fun v => v.val) at hx
    rcases List.mem_map.mp hx with ⟨v, hv, rfl⟩
    exact hm v hv
  have hcc : ∀ x ∈ woutColumn W l.val k.val, -(74 : Int) ≤ x ∧ x ≤ 74 := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨row, hrow, rfl⟩
    have hlay : (W.layers.val[l.val]!) = W.layers.val[l.val]'(by simpa using hl) :=
      getElem!_pos _ l.val (by simp; omega)
    rw [hlay] at hrow
    have hwm := hL.wout row hrow
    have hmem2 : (row.val[k.val]!) ∈ row.val := by
      rw [getElem!_pos _ k.val (by simp; omega)]
      exact List.getElem_mem (by simp; omega)
    exact hwm _ hmem2
  have hbd : -8160491678340218880 ≤ GeneralModel.dot (ints m)
      (woutColumn W l.val k.val) ∧
      GeneralModel.dot (ints m) (woutColumn W l.val k.val) ≤
        8160491678340218880 := by
    have hd := project_dot_bound (ints m) (woutColumn W l.val k.val)
      Envelope.hidden 74 (by simp only [Envelope.hidden]; norm_num)
      (by norm_num) hrc hcc
    rw [ints_length512] at hd
    simp only [Envelope.hidden] at hd
    have hnum : 512 * (215384598773760 * 74) = 8160491678340218880 := by norm_num
    omega
  unfold general_engine.mlp_output_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (st : I64 × Usize) => 512 - st.2.val)
    (inv := fun (st : I64 × Usize) =>
      st.2.val ≤ 512 ∧
      st.1.val + GeneralModel.dot ((ints m).drop st.2.val)
          ((woutColumn W l.val k.val).drop st.2.val) =
        GeneralModel.dot (ints m) (woutColumn W l.val k.val) ∧
      -(215384598773760 * 74) * (st.2.val : Int) ≤ st.1.val ∧
      st.1.val ≤ (215384598773760 * 74) * (st.2.val : Int))
  · rintro ⟨acc, t⟩ ⟨ht1, hacc, hlo, hhi⟩
    unfold general_engine.mlp_output_loop0_loop0.body
    dsimp only at ht1 hacc hlo hhi ⊢
    simp only [general_engine.D_MLP]
    split
    · have ht512 : t.val < 512 := by scalar_tac
      rw [dot_drop _ _ _ (by rw [ints_length512]; omega)
        (by rw [woutColumn_length]; omega)] at hacc
      step as ⟨i1v, hi1⟩
      step as ⟨lw, hlw⟩
      subst hlw
      step as ⟨a, ha⟩
      step as ⟨i2v, hi2⟩
      step as ⟨i3v, hi3⟩
      have hi3v' : i3v.val = i2v.val := by scalar_tac
      have hmem : i1v.val ∈ (ints m) := by
        change i1v.val ∈ m.val.map (fun v => v.val)
        refine List.mem_map.mpr ⟨m.val[t.val]!, ?_, ?_⟩
        · rw [getElem!_pos _ t.val (by simp; omega)]
          exact List.getElem_mem (by simp; omega)
        · rw [getElem!_pos _ t.val (by simp; omega), hi1]
      have hrb : -215384598773760 ≤ i1v.val ∧ i1v.val ≤ 215384598773760 :=
        hrc _ hmem
      have hxi : (ints m)[t.val]'(by rw [ints_length512]; omega) = i1v.val := by
        simp only [ints, List.getElem_map]
        rw [hi1]
      have hlay : (W.layers.val[l.val]!) = W.layers.val[l.val]'(by simpa using hl) :=
        getElem!_pos _ l.val (by simp; omega)
      have hwout : ((W.layers.val[l.val]!).wout.val[t.val]!) = a := by
        rw [hlay]
        rw [getElem!_pos _ t.val (by simp; omega)]
        exact ha.symm
      have hcol : (woutColumn W l.val k.val)[t.val]'(by rw [woutColumn_length]; omega)
          = i3v.val :=
        wout_column_entry_probe W l t k ht512 hk a i2v i3v hwout hi2 hi3v'
      have hcb : -(74 : Int) ≤ i3v.val ∧ i3v.val ≤ 74 := by
        have hct := hcc _ (List.getElem_mem (by rw [woutColumn_length]; omega))
        rw [hcol] at hct
        exact hct
      have hprod : -(215384598773760 * 74) ≤ i1v.val * i3v.val ∧
          i1v.val * i3v.val ≤ 215384598773760 * 74 := by
        constructor <;> nlinarith [mul_nonneg (by omega : 0 ≤ i1v.val + 215384598773760)
          (by omega : 0 ≤ i3v.val + 74),
          mul_nonneg (by omega : 0 ≤ i1v.val + 215384598773760) (by omega : 0 ≤ 74 - i3v.val),
          mul_nonneg (by omega : 0 ≤ 215384598773760 - i1v.val) (by omega : 0 ≤ i3v.val + 74),
          mul_nonneg (by omega : 0 ≤ 215384598773760 - i1v.val) (by omega : 0 ≤ 74 - i3v.val)]
      have hminb : I64.min ≤ i1v.val * i3v.val := by
        have hpp := hprod
        scalar_tac
      have hmaxb : i1v.val * i3v.val ≤ I64.max := by
        have hpp := hprod
        scalar_tac
      step with I64.mul_spec hminb hmaxb as ⟨i4, hi4⟩
      have hmina : I64.min ≤ acc.val + i4.val := by
        have hpp : -(215384598773760 * 74) * 512 ≤ i1v.val * i3v.val + acc.val := by
          have h1 := hprod.1
          omega
        scalar_tac
      have hmaxa : acc.val + i4.val ≤ I64.max := by
        have hpp := hprod
        scalar_tac
      step with I64.add_spec hmina hmaxa as ⟨acc1, hacc1⟩
      step as ⟨t1, ht1'⟩
      have ht1v : t1.val = t.val + 1 := by scalar_tac
      rw [hxi, hcol] at hacc
      rw [ht1v]
      have hp' : i4.val = i1v.val * i3v.val := by scalar_tac
      have hnew : acc1.val = acc.val + i4.val := by scalar_tac
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · exact mlp_tail_linear_probe acc.val i1v.val i3v.val acc1.val i4.val
          (GeneralModel.dot ((ints m).drop (t.val + 1)) ((woutColumn W l.val k.val).drop (t.val + 1)))
          (GeneralModel.dot (ints m) (woutColumn W l.val k.val)) hacc hp' hnew
      · have hacc2 : acc1.val + GeneralModel.dot ((ints m).drop (t.val + 1))
            ((woutColumn W l.val k.val).drop (t.val + 1)) =
          GeneralModel.dot (ints m) (woutColumn W l.val k.val) :=
          mlp_tail_linear_probe acc.val i1v.val i3v.val acc1.val i4.val
            (GeneralModel.dot ((ints m).drop (t.val + 1)) ((woutColumn W l.val k.val).drop (t.val + 1)))
            (GeneralModel.dot (ints m) (woutColumn W l.val k.val)) hacc hp' hnew
        have hacc3 : acc1.val = acc.val + i1v.val * i3v.val := by
          rw [hnew, hp']
        have h1 := hlo
        have h2 := hprod.1
        omega
      · have hacc2 : acc1.val + GeneralModel.dot ((ints m).drop (t.val + 1))
            ((woutColumn W l.val k.val).drop (t.val + 1)) =
          GeneralModel.dot (ints m) (woutColumn W l.val k.val) :=
          mlp_tail_linear_probe acc.val i1v.val i3v.val acc1.val i4.val
            (GeneralModel.dot ((ints m).drop (t.val + 1)) ((woutColumn W l.val k.val).drop (t.val + 1)))
            (GeneralModel.dot (ints m) (woutColumn W l.val k.val)) hacc hp' hnew
        have hacc3 : acc1.val = acc.val + i1v.val * i3v.val := by
          rw [hnew, hp']
        have h1 := hhi
        have h2 := hprod.2
        omega
    · have ht512 : t.val = 512 := by scalar_tac
      simp only [WP.spec_ok]
      rw [ht512] at hacc
      have hdz : ((ints m).drop 512) = [] := by simp [ints_length512]
      have hdc : ((woutColumn W l.val k.val).drop 512) = [] := by
        simp [woutColumn_length]
      rw [hdz, hdc] at hacc
      have hdot : acc.val = GeneralModel.dot (ints m) (woutColumn W l.val k.val) := by
        simpa [GeneralModel.dot] using hacc
      refine ⟨trivial, hdot, ?_, ?_⟩
      · rw [hdot]; exact hbd.1
      · rw [hdot]; exact hbd.2
  · simp only
    refine ⟨by scalar_tac, ?_, by norm_num, by norm_num⟩
    show (0 : Int) + GeneralModel.dot (ints m) (woutColumn W l.val k.val) =
        GeneralModel.dot (ints m) (woutColumn W l.val k.val)
    omega

end LcnExec.GeneralEngine
