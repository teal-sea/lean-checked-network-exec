import LcnExec.GeneralEngine.MlpOutputInner

set_option maxHeartbeats 800000

/-!
# The MLP output projection `general_engine.mlp_output`

The 128-coordinate outer scan: per output the checked dot (weights threaded and
returned equal), the unscaled signed bias `bout[k]`, the checked add and write.
Exact `GeneralModel.mlpOutput` and `Bounded Envelope.mlp_output`.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace LcnExec.GeneralEngine

theorem ints_length128' (m : Array I64 128#usize) : (ints m).length = 128 :=
  ints_length128 m

def woutRowsProbe (W : general_engine.Weights) (l : Usize) :=
  (W.layers.val[l.val]!).wout.val.map (fun row => row.val.map (·.val))

theorem woutRows_model_probe (W : general_engine.Weights) (l : Usize) (hl : l.val < 2) :
    (GeneralModel.layer (toGeneralModel W) l.val).wout = woutRowsProbe W l := by
  rw [model_layer_eq W l hl]
  simp only [toLayerModel, woutRowsProbe]
  rw [getElem!_pos W.layers.val l.val (by rw [Array.length_eq]; exact hl)]

theorem woutRows_width_probe (W : general_engine.Weights) (l : Usize) (row : List Int)
    (hm : row ∈ woutRowsProbe W l) : row.length = 128 := by
  rcases List.mem_map.mp hm with ⟨v, _, rfl⟩
  simp

theorem woutColumn_model_probe (W : general_engine.Weights) (l : Usize) (i : Nat)
    (hi : i < 128) :
    woutColumn W l.val i = (woutRowsProbe W l).map (fun row => GeneralModel.nth 0 row i) := by
  unfold woutRowsProbe woutColumn
  rw [List.map_map]
  apply List.map_congr_left
  intro row _
  rw [Function.comp_apply, project_nth_eq 0 (row.val.map (·.val)) i
      (by rw [List.length_map, Array.length_eq]; exact hi)]
  simp only [List.getElem_map]
  rw [getElem!_pos row.val i (by rw [Array.length_eq]; exact hi)]

theorem bout_read_signed_probe (W : general_engine.Weights) (hW : LoadBounds W)
    (l k : Usize) (hl : l.val < 2) (hk : k.val < 128) :
    let lw := W.layers.val[l.val]'(by rw [Array.length_eq]; exact hl)
    let b := lw.bout.val[k.val]'(by rw [Array.length_eq]; exact hk)
    GeneralModel.nth 0 (GeneralModel.layer (toGeneralModel W) l.val).bout k.val = b.val ∧
      -137438953472 ≤ b.val ∧ b.val ≤ 137438953472 := by
  dsimp only
  refine ⟨?_, (layerBounds hW l hl).bout _ (List.getElem_mem _)⟩
  rw [model_layer_eq W l hl]
  simp only [toLayerModel]
  rw [project_nth_eq _ _ _ (by rw [List.length_map, Array.length_eq]; exact hk)]
  simp only [List.getElem_map]

theorem mlpOutput_length (W : general_engine.Weights) (l : Usize) (hl : l.val < 2)
    (m : List Int) :
    (GeneralModel.mlpOutput (toGeneralModel W) l.val m).length = 128 := by
  have hw := woutRows_model_probe W l hl
  have ht : (GeneralModel.lincomb 128 m (woutRowsProbe W l)).length = 128 :=
    project_lincomb_length 128 m (woutRowsProbe W l) (woutRows_width_probe W l)
  have hb : (GeneralModel.layer (toGeneralModel W) l.val).bout.length = 128 := by
    rw [model_layer_eq W l hl]
    simp [toLayerModel]
  simp only [GeneralModel.mlpOutput, hw]
  rw [project_addV_length _ _ (ht.trans hb.symm), ht]

theorem mlp_output_entry_probe (W : general_engine.Weights) (l : Usize)
    (hl : l.val < 2) (m : List Int) (k : Nat) (hk : k < 128) :
    (GeneralModel.mlpOutput (toGeneralModel W) l.val m)[k]'
        (by rw [mlpOutput_length W l hl]; exact hk) =
      GeneralModel.dot m (woutColumn W l.val k) +
        GeneralModel.nth 0 (GeneralModel.layer (toGeneralModel W) l.val).bout k := by
  have hw := woutRows_model_probe W l hl
  have ht : (GeneralModel.lincomb 128 m (woutRowsProbe W l)).length = 128 :=
    project_lincomb_length 128 m (woutRowsProbe W l) (woutRows_width_probe W l)
  have hb : (GeneralModel.layer (toGeneralModel W) l.val).bout.length = 128 := by
    rw [model_layer_eq W l hl]
    simp [toLayerModel]
  have hxs : k < (GeneralModel.lincomb 128 m (woutRowsProbe W l)).length := by
    rw [ht]; exact hk
  have hbs : k < (GeneralModel.layer (toGeneralModel W) l.val).bout.length := by
    rw [hb]; exact hk
  have hentry := project_addV_get
    (GeneralModel.lincomb 128 m (woutRowsProbe W l))
    (GeneralModel.layer (toGeneralModel W) l.val).bout (ht.trans hb.symm) k hxs
  have hdot : (GeneralModel.lincomb 128 m (woutRowsProbe W l))[k]'hxs =
      GeneralModel.dot m (woutColumn W l.val k) := by
    rw [project_lincomb_get 128 m (woutRowsProbe W l) (woutRows_width_probe W l) k hk,
      woutColumn_model_probe W l k hk]
  have hbout : (GeneralModel.layer (toGeneralModel W) l.val).bout[k]'hbs =
      GeneralModel.nth 0 (GeneralModel.layer (toGeneralModel W) l.val).bout k :=
    (project_nth_eq _ _ _ hbs).symm
  simp only [GeneralModel.mlpOutput, hw]
  rw [hentry, hdot, hbout]

theorem mlp_output_spec (W : general_engine.Weights) (hW : LoadBounds W)
    (l : Usize) (hl : l.val < 2)
    (m : Array I64 512#usize) (hm : Bounded Envelope.hidden m) :
    general_engine.mlp_output W l m ⦃ o =>
      ints o = GeneralModel.mlpOutput (toGeneralModel W) l.val (ints m) ∧
      Bounded Envelope.mlp_output o ⦄ := by
  have hL := layerBounds hW l hl
  unfold general_engine.mlp_output general_engine.mlp_output_loop0
  apply loop.spec_decr_nat
    (measure := fun (st : general_engine.Weights × Array I64 128#usize × Usize) =>
      128 - st.2.2.val)
    (inv := fun (st : general_engine.Weights × Array I64 128#usize × Usize) =>
      st.2.2.val ≤ 128 ∧
      st.1 = W ∧
      Bounded Envelope.mlp_output st.2.1 ∧
      (∀ (k : Nat) (hk : k < 128) (hik : k < st.2.2.val),
        (ints st.2.1)[k]'(by rw [ints_length128]; omega) =
          GeneralModel.dot (ints m) (woutColumn W l.val k) +
            GeneralModel.nth 0 (GeneralModel.layer (toGeneralModel W) l.val).bout k) ∧
      (∀ (k : Nat) (hk : k < 128) (hik : ¬ k < st.2.2.val),
        st.2.1.val[k]'(by simp; omega) = 0#i64))
  · rintro ⟨w1, o1, k1⟩ ⟨hi1, hw, hbd, heq, hsuf⟩
    unfold general_engine.mlp_output_loop0.body
    dsimp only at hi1 hw hbd heq hsuf ⊢
    simp only [general_engine.D_MODEL]
    split
    · have hk128 : k1.val < 128 := by scalar_tac
      have hwL : LoadBounds w1 := by rw [hw]; exact hW
      step with mlp_output_inner_spec w1 hwL l hl m hm k1 hk128 as
        ⟨w2, acc, hw2, hdot, hlo, hhi⟩
      step as ⟨lw, hlw⟩
      subst hlw
      step as ⟨iv, hiv⟩
      rw [hw2, hw] at hiv
      have hread : iv =
          (W.layers.val[l.val]'(by rw [Array.length_eq]; exact hl)).bout.val[k1.val]'
            (by rw [Array.length_eq]; exact hk128) := hiv
      have hbout : iv.val =
          GeneralModel.nth 0 (GeneralModel.layer (toGeneralModel W) l.val).bout k1.val ∧
          -137438953472 ≤ iv.val ∧ iv.val ≤ 137438953472 := by
        have hmodel := bout_read_signed_probe W hW l k1 hl hk128
        have hb := congrArg (fun v : I64 => v.val) hread
        rw [hb]
        exact ⟨hmodel.1.symm, hmodel.2⟩
      have hdotW : acc.val = GeneralModel.dot (ints m) (woutColumn W l.val k1.val) :=
        by simpa only [hw] using hdot
      have hmina : I64.min ≤ acc.val + iv.val := by
        have h1 : -8160491678340218880 ≤ acc.val := hlo
        have h2 := hbout.2.1
        scalar_tac
      have hmaxa : acc.val + iv.val ≤ I64.max := by
        have h1 : acc.val ≤ 8160491678340218880 := hhi
        have h2 := hbout.2.2
        scalar_tac
      step with I64.add_spec hmina hmaxa as ⟨i1, hi1v⟩
      step with Array.update_spec o1 k1 i1 (by simp; omega) as ⟨o2, ho2⟩
      step as ⟨k2, hk2⟩
      have hk2v : k2.val = k1.val + 1 := by scalar_tac
      simp only [hk2v]
      have hbv : -Envelope.mlp_output ≤ i1.val ∧ i1.val ≤ Envelope.mlp_output := by
        have h1 : -8160491678340218880 ≤ acc.val := hlo
        have h2 : acc.val ≤ 8160491678340218880 := hhi
        have h3 := hbout.2
        have hrw : i1.val = acc.val + iv.val := by rw [hi1v]
        change -8160491815779172352 ≤ i1.val ∧ i1.val ≤ 8160491815779172352
        omega
      refine ⟨by omega, hw2.trans hw, ?_, ?_, ?_, by omega⟩
      · rw [ho2]
        exact project_bounded_set _ _ _ _ hbd hbv
      · intro k hk hik
        by_cases hkk : k = k1.val
        · subst k
          have hset : (ints o2)[k1.val]'(by rw [ints_length128]; omega) = i1.val := by
            rw [ho2]
            simp only [ints, Array.set_val_eq, List.getElem_map]
            rw [List.getElem_set_self (by simp; omega)]
          rw [hset, hi1v, hdotW, ← hbout.1]
        · have hval : (ints o2)[k]'(by rw [ints_length128]; omega) =
              (ints o1)[k]'(by rw [ints_length128]; omega) := by
            rw [ho2]
            simp only [ints, Array.set_val_eq, List.getElem_map]
            rw [List.getElem_set_ne (by omega)]
          rw [hval]
          exact heq k hk (by omega)
      · intro k hk hik
        have hval : o2.val[k]'(by simp; omega) = o1.val[k]'(by simp; omega) := by
          rw [ho2]
          simp only [Array.set_val_eq]
          rw [List.getElem_set_ne (by omega)]
        rw [hval]
        exact hsuf k hk (by omega)
    · have hk128 : k1.val = 128 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, hbd⟩
      apply List.ext_getElem
      · rw [ints_length128, mlpOutput_length W l hl]
      · intro k hk' hk''
        rw [ints_length128] at hk'
        have hk128' : k < 128 := by omega
        have hentry := mlp_output_entry_probe W l hl (ints m) k hk128'
        have hinvk := heq k hk128' (by omega)
        rw [hentry, hinvk]
  · simp only
    refine ⟨by scalar_tac, trivial, ?_, ?_, ?_⟩
    · intro v hv
      rw [repeat_val_probe] at hv
      rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
      constructor <;> simp only [Envelope.mlp_output] <;> norm_num
    · intro k hk hik
      exact absurd hik (by show ¬(k < 0); omega)
    · intro k hk hik
      have hz : ∀ x ∈ (Array.repeat 128#usize 0#i64).val, x = 0#i64 := by
        intro x hx
        rw [repeat_val_probe] at hx
        exact (List.mem_replicate.mp hx).2
      exact hz _ (List.getElem_mem (by simp; omega))

end LcnExec.GeneralEngine
