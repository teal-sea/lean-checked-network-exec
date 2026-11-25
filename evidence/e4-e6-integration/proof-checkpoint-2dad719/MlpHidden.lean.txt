import LcnExec.GeneralEngine.MlpHiddenInner

set_option maxHeartbeats 800000

/-!
# The MLP hidden layer `general_engine.mlp_hidden`
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace LcnExec.GeneralEngine

theorem ints_length512 (m : Array I64 512#usize) : (ints m).length = 512 := by
  simp [ints]

def winRowsProbe (W : general_engine.Weights) (l : Usize) :=
  (W.layers.val[l.val]!).win.val.map (fun row => row.val.map (·.val))

theorem hidden_length_probe (xs ys : List Int) (h : xs.length = ys.length) :
    (GeneralModel.hidden xs ys).length = xs.length := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          have hs : xs.length = ys.length := by simpa using h
          simpa [GeneralModel.hidden] using ih ys hs

theorem winRows_model_probe (W : general_engine.Weights) (l : Usize) (hl : l.val < 2) :
    (GeneralModel.layer (toGeneralModel W) l.val).win = winRowsProbe W l := by
  rw [model_layer_eq W l hl]
  simp only [toLayerModel, winRowsProbe]
  rw [getElem!_pos W.layers.val l.val (by rw [Array.length_eq]; exact hl)]

theorem winRows_width_probe (W : general_engine.Weights) (l : Usize) (row : List Int)
    (hm : row ∈ winRowsProbe W l) : row.length = 512 := by
  rcases List.mem_map.mp hm with ⟨v, _, rfl⟩
  simp

theorem winColumn_model_probe (W : general_engine.Weights) (l : Usize) (i : Nat)
    (hi : i < 512) :
    winColumn W l.val i = (winRowsProbe W l).map (fun row => GeneralModel.nth 0 row i) := by
  unfold winRowsProbe winColumn
  rw [List.map_map]
  apply List.map_congr_left
  intro row _
  rw [Function.comp_apply, project_nth_eq 0 (row.val.map (·.val)) i
      (by rw [List.length_map, Array.length_eq]; exact hi)]
  simp only [List.getElem_map]
  rw [getElem!_pos row.val i (by rw [Array.length_eq]; exact hi)]

theorem bin_read_signed_probe (W : general_engine.Weights) (hW : LoadBounds W)
    (l i : Usize) (hl : l.val < 2) (hi : i.val < 512) :
    let lw := W.layers.val[l.val]'(by rw [Array.length_eq]; exact hl)
    let b := lw.bin.val[i.val]'(by rw [Array.length_eq]; exact hi)
    GeneralModel.nth 0 (GeneralModel.layer (toGeneralModel W) l.val).bin i.val = b.val ∧
      -1073741824 ≤ b.val ∧ b.val ≤ 1073741824 := by
  dsimp only
  refine ⟨?_, (layerBounds hW l hl).bin _ (List.getElem_mem _)⟩
  rw [model_layer_eq W l hl]
  simp only [toLayerModel]
  rw [project_nth_eq _ _ _ (by rw [List.length_map, Array.length_eq]; exact hi)]
  simp only [List.getElem_map]

theorem hidden_mapped_length_probe (W : general_engine.Weights) (l : Usize)
    (hl : l.val < 2) (r : List Int) :
    (GeneralModel.mlpHidden (toGeneralModel W) l.val r).length = 512 := by
  have ht := project_lincomb_length 512 r (winRowsProbe W l) (winRows_width_probe W l)
  have hb : (GeneralModel.layer (toGeneralModel W) l.val).bin.length = 512 := by
    rw [model_layer_eq W l hl]
    simp [toLayerModel]
  simp only [GeneralModel.mlpHidden, winRows_model_probe W l hl]
  rw [hidden_length_probe _ _ (ht.trans hb.symm), ht]

theorem hidden_activation_bang_probe : ∀ (xs ys : List Int) (k : Nat),
    k < xs.length → k < ys.length →
    (GeneralModel.hidden xs ys)[k]! =
      (let pre := xs[k]! + ys[k]! * 256
       if pre > 0 then Int.shiftRight pre 8 else 0)
  | [], _, _, hx, _ => by simp at hx
  | _ :: _, [], _, _, hy => by simp at hy
  | _ :: _, _ :: _, 0, _, _ => by simp [GeneralModel.hidden]
  | x :: xs, y :: ys, k + 1, hx, hy => by
      simp only [List.length_cons] at hx hy
      simpa [GeneralModel.hidden] using hidden_activation_bang_probe xs ys k (by omega) (by omega)

theorem hidden_shift_bound_probe (pre : Int) (hp : 0 < pre) (hb : pre ≤ Envelope.hidden_pre) :
    0 ≤ Int.shiftRight pre 8 ∧ Int.shiftRight pre 8 ≤ Envelope.hidden := by
  have hs : Int.shiftRight pre 8 = pre / 256 := Int.shiftRight_eq_div_pow pre 8
  rw [hs]
  change 0 ≤ pre / 256 ∧ pre / 256 ≤ 215384598773760
  change pre ≤ 55138457286082560 at hb
  omega

theorem repeat_val_probe (n : Usize) (v : I64) :
    (Array.repeat n v).val = List.replicate n.val v := by
  simp [Array.repeat]

theorem repeat_zero_index_probe (k : Nat) (hk : k < 512) :
    (Array.repeat 512#usize 0#i64).val[k]'(by rw [Array.length_eq]; exact hk) = 0#i64 := by
  have hz : ∀ x ∈ (Array.repeat 512#usize 0#i64).val, x = 0#i64 := by
    intro x hx
    rw [repeat_val_probe] at hx
    exact (List.mem_replicate.mp hx).2
  exact hz _ (List.getElem_mem _)

theorem repeat_zero_bounded_probe : Bounded Envelope.hidden (Array.repeat 512#usize 0#i64) := by
  intro v hv
  rw [repeat_val_probe] at hv
  rcases List.mem_replicate.mp hv with ⟨_, rfl⟩
  constructor <;> simp only [Envelope.hidden] <;> norm_num

theorem hidden_runtime_bias_probe (W : general_engine.Weights) (hW : LoadBounds W)
    (l i : Usize) (hl : l.val < 2) (hi : i.val < 512) (b : I64)
    (hread : b = (W.layers.val[l.val]'(by rw [Array.length_eq]; exact hl)).bin.val[i.val]'
      (by rw [Array.length_eq]; exact hi)) :
    b.val = GeneralModel.nth 0 (GeneralModel.layer (toGeneralModel W) l.val).bin i.val ∧
      -1073741824 ≤ b.val ∧ b.val ≤ 1073741824 := by
  have hmodel := bin_read_signed_probe W hW l i hl hi
  have hb := congrArg (fun v : I64 => v.val) hread
  rw [hb]
  exact ⟨hmodel.1.symm, hmodel.2⟩

theorem hidden_mapped_entry_probe (W : general_engine.Weights) (l : Usize)
    (hl : l.val < 2) (r : List Int) (k : Nat) (hk : k < 512) :
    (GeneralModel.mlpHidden (toGeneralModel W) l.val r)[k]'
        (by rw [hidden_mapped_length_probe W l hl]; exact hk) =
      (let pre := GeneralModel.dot r (winColumn W l.val k) +
          GeneralModel.nth 0 (GeneralModel.layer (toGeneralModel W) l.val).bin k * 256
       if pre > 0 then Int.shiftRight pre 8 else 0) := by
  let xs := GeneralModel.lincomb 512 r (winRowsProbe W l)
  let bs := (GeneralModel.layer (toGeneralModel W) l.val).bin
  have hxs : xs.length = 512 :=
    project_lincomb_length 512 r (winRowsProbe W l) (winRows_width_probe W l)
  have hbs : bs.length = 512 := by
    dsimp only [bs]
    rw [model_layer_eq W l hl]
    simp [toLayerModel]
  have hx : k < xs.length := by rw [hxs]; exact hk
  have hb : k < bs.length := by rw [hbs]; exact hk
  have hh : k < (GeneralModel.hidden xs bs).length := by
    rw [hidden_length_probe xs bs (hxs.trans hbs.symm)]; exact hx
  have hentry := hidden_activation_bang_probe xs bs k hx hb
  rw [getElem!_pos (GeneralModel.hidden xs bs) k hh, getElem!_pos xs k hx,
    getElem!_pos bs k hb] at hentry
  have hdot : xs[k]'hx = GeneralModel.dot r (winColumn W l.val k) := by
    change (GeneralModel.lincomb 512 r (winRowsProbe W l))[k]'hx = _
    rw [project_lincomb_get 512 r (winRowsProbe W l) (winRows_width_probe W l) k hk,
      winColumn_model_probe W l k hk]
  rw [← project_nth_eq 0 bs k hb, hdot] at hentry
  simpa only [GeneralModel.mlpHidden, winRows_model_probe W l hl, xs, bs] using hentry

theorem activation_compare_probe (pre : I64) : (pre > 0#i64) ↔ (0 : Int) < pre.val := by
  change (0 : Int) < pre.val ↔ (0 : Int) < pre.val
  exact Iff.rfl

theorem activation_upper_probe (pre : I64) (hb : pre.val ≤ 55138457286082560) :
    pre.val ≤ Envelope.hidden_pre := hb

theorem activation_write_bound_probe {n : Usize} (m a : Array I64 n) (i : Usize)
    (pre v : I64) (hm : a = m.set i v) (hbd : Bounded Envelope.hidden m)
    (hs : v.val = Int.shiftRight pre.val 8) (hp : pre > 0#i64)
    (hb : pre.val ≤ 55138457286082560) : Bounded Envelope.hidden a := by
  obtain ⟨hlo, hhi⟩ := hidden_shift_bound_probe pre.val
    ((activation_compare_probe pre).mp hp) (activation_upper_probe pre hb)
  have hv : -Envelope.hidden ≤ v.val ∧ v.val ≤ Envelope.hidden := by
    rw [hs]
    have hb0 : 0 ≤ Envelope.hidden := by simp [Envelope.hidden]
    omega
  rw [hm]
  exact project_bounded_set _ _ _ _ hbd hv

theorem mlp_hidden_spec (W : general_engine.Weights) (hW : LoadBounds W)
    (l : Usize) (hl : l.val < 2)
    (r : Array I64 128#usize) (hr : Bounded Envelope.residual r) :
    general_engine.mlp_hidden W l r ⦃ m =>
      ints m = GeneralModel.mlpHidden (toGeneralModel W) l.val (ints r) ∧
      Bounded Envelope.hidden m ⦄ := by
  have hL := layerBounds hW l hl
  have hrb : ∀ x ∈ (ints r), -Envelope.residual ≤ x ∧ x ≤ Envelope.residual := by
    intro x hx
    change x ∈ r.val.map (fun v => v.val) at hx
    rcases List.mem_map.mp hx with ⟨v, hv, rfl⟩
    exact hr v hv
  have hcc : ∀ (i : Usize), i.val < 512 → ∀ x ∈ winColumn W l.val i.val,
      -(82 : Int) ≤ x ∧ x ≤ 82 := by
    intro i hi x hx
    rcases List.mem_map.mp hx with ⟨row, hrow, rfl⟩
    have hlay : (W.layers.val[l.val]!) = W.layers.val[l.val]'(by simpa using hl) :=
      getElem!_pos _ l.val (by simp; omega)
    rw [hlay] at hrow
    have hwm := hL.win row hrow
    have hmem2 : (row.val[i.val]!) ∈ row.val := by
      rw [getElem!_pos _ i.val (by simp; omega)]
      exact List.getElem_mem (by simp; omega)
    exact hwm _ hmem2
  unfold general_engine.mlp_hidden general_engine.mlp_hidden_loop0
  apply loop.spec_decr_nat
    (measure := fun (st : general_engine.Weights × Array I64 512#usize × Usize) =>
      512 - st.2.2.val)
    (inv := fun (st : general_engine.Weights × Array I64 512#usize × Usize) =>
      st.2.2.val ≤ 512 ∧
      st.1 = W ∧
      Bounded Envelope.hidden st.2.1 ∧
      (∀ (k : Nat) (hk : k < 512) (hik : k < st.2.2.val),
        (ints st.2.1)[k]'(by rw [ints_length512]; omega) =
          (let pre := GeneralModel.dot (ints r) (winColumn W l.val k) +
              GeneralModel.nth 0 (GeneralModel.layer (toGeneralModel W) l.val).bin k * 256
           if pre > 0 then Int.shiftRight pre 8 else 0)) ∧
      (∀ (k : Nat) (hk : k < 512) (hik : ¬ k < st.2.2.val),
        st.2.1.val[k]'(by simp; omega) = 0#i64))
  · rintro ⟨w1, m1, i1⟩ ⟨hi1, hw, hbd, heq, hsuf⟩
    unfold general_engine.mlp_hidden_loop0.body
    dsimp only at hi1 hw hbd heq hsuf ⊢
    simp only [general_engine.D_MLP]
    split
    · have hi512 : i1.val < 512 := by scalar_tac
      have hwL : LoadBounds w1 := by rw [hw]; exact hW
      step with mlp_hidden_inner_spec w1 hwL l hl r hr i1 hi512 as
        ⟨w2, acc, hw2, hdot, hlo, hhi⟩
      step as ⟨lw, hlw⟩
      subst hlw
      step as ⟨i1v, hi1v⟩
      rw [hw2, hw] at hi1v
      have hread : i1v =
          (W.layers.val[l.val]'(by rw [Array.length_eq]; exact hl)).bin.val[i1.val]'
            (by rw [Array.length_eq]; exact hi512) := hi1v
      have hbinv : i1v.val =
          GeneralModel.nth 0 (GeneralModel.layer (toGeneralModel W) l.val).bin i1.val ∧
          -1073741824 ≤ i1v.val ∧ i1v.val ≤ 1073741824 :=
        hidden_runtime_bias_probe W hW l i1 hl hi512 i1v hread
      have hbinv' : i1v.val =
          GeneralModel.nth 0 (GeneralModel.layer (toGeneralModel W) l.val).bin i1.val :=
        hbinv.1
      have hbb : -1073741824 ≤ i1v.val ∧ i1v.val ≤ 1073741824 := hbinv.2
      have hdotW : acc.val = GeneralModel.dot (ints r) (winColumn W l.val i1.val) :=
        by simpa only [hw] using hdot
      have hdotcap : -55138182408175616 ≤ acc.val ∧ acc.val ≤ 55138182408175616 := by
        rw [hdotW]
        have hd := project_dot_bound (ints r) (winColumn W l.val i1.val)
          Envelope.residual 82 (by simp only [Envelope.residual]; norm_num)
          (by norm_num) hrb (hcc i1 hi512)
        rw [ints_length128] at hd
        simp only [Envelope.residual] at hd
        have hnum : 128 * (5253256708096 * 82) = 55138182408175616 := by norm_num
        omega
      have hminm : I64.min ≤ i1v.val * (256#i64).val := by
        have hpp := hbb
        scalar_tac
      have hmaxm : i1v.val * (256#i64).val ≤ I64.max := by
        have hpp := hbb
        scalar_tac
      step with I64.mul_spec hminm hmaxm as ⟨i2, hi2⟩
      have hbi2 : -274877906944 ≤ i2.val ∧ i2.val ≤ 274877906944 := by
        rw [hi2]
        change -1073741824 * 256 ≤ i1v.val * 256 ∧ i1v.val * 256 ≤ 1073741824 * 256
        have h3 := hbb
        omega
      have hmina : I64.min ≤ acc.val + i2.val := by
        have h1 := hdotcap
        have h2 := hbi2
        scalar_tac
      have hmaxa : acc.val + i2.val ≤ I64.max := by
        have h1 := hdotcap
        have h2 := hbi2
        scalar_tac
      step with I64.add_spec hmina hmaxa as ⟨pre, hpre⟩
      have hpreb : -55138457286082560 ≤ pre.val ∧ pre.val ≤ 55138457286082560 := by
        have h1 := hdotcap
        have h2 := hbi2
        rw [hpre]
        omega
      have hmodelPre : GeneralModel.dot (ints r) (winColumn W l.val i1.val) +
          GeneralModel.nth 0 (GeneralModel.layer (toGeneralModel W) l.val).bin i1.val * 256
            = pre.val := by
        rw [hpre, hi2, ← hdotW, ← hbinv']
      by_cases hp : pre > 0#i64
      · rw [ite_eq_left hp]
        step as ⟨i3, hshift⟩
        have hshiftv : i3.val = Int.shiftRight pre.val 8 := by
          rw [hshift]
          rfl
        step with Array.update_spec m1 i1 i3 (by simp; omega) as ⟨m2, hm2⟩
        have hsb := activation_write_bound_probe m1 m2 i1 pre i3 hm2 hbd hshiftv hp
          hpreb.2
        step as ⟨i4, hi4⟩
        have hi4v : i4.val = i1.val + 1 := by scalar_tac
        simp only [hi4v]
        refine ⟨by omega, hw2.trans hw, hsb, ?_, ?_, by omega⟩
        · intro k hk hik
          by_cases hkk : k = i1.val
          · subst k
            have hset : (ints m2)[i1.val]'(by rw [ints_length512]; omega) = i3.val := by
              rw [hm2]
              simp only [ints, Array.set_val_eq, List.getElem_map]
              rw [List.getElem_set_self (by simp; omega)]
            rw [hset, hshiftv, hmodelPre, ite_eq_left ((activation_compare_probe pre).mp hp)]
          · have hval : (ints m2)[k]'(by rw [ints_length512]; omega) =
                (ints m1)[k]'(by rw [ints_length512]; omega) := by
              rw [hm2]
              simp only [ints, Array.set_val_eq, List.getElem_map]
              rw [List.getElem_set_ne (by omega)]
            rw [hval]
            exact heq k hk (by omega)
        · intro k hk hik
          have hval : m2.val[k]'(by simp; omega) = m1.val[k]'(by simp; omega) := by
            rw [hm2]
            simp only [Array.set_val_eq]
            rw [List.getElem_set_ne (by omega)]
          rw [hval]
          exact hsuf k hk (by omega)
      · rw [ite_eq_right hp]
        step as ⟨i4, hi4⟩
        have hi4v : i4.val = i1.val + 1 := by scalar_tac
        simp only [hi4v]
        refine ⟨by omega, hw2.trans hw, hbd, ?_, ?_, by omega⟩
        · intro k hk hik
          by_cases hkk : k = i1.val
          · subst k
            have hz := hsuf i1.val hi512 (Nat.lt_irrefl _)
            have hzv : (ints m1)[i1.val]'(by rw [ints_length512]; omega) =
                (0 : Int) := by
              have hc := congrArg (fun x : I64 => x.val) hz
              have hd : (ints m1)[i1.val]'(by rw [ints_length512]; omega) =
                  (m1.val[i1.val]'(by simp; omega)).val := by
                simp only [ints, List.getElem_map]
              rw [hd]
              exact hc
            rw [hzv, hmodelPre,
              ite_eq_right (fun h => hp ((activation_compare_probe pre).mpr h))]
          · exact heq k hk (by omega)
        · intro k hk hik
          exact hsuf k hk (by omega)
    · have hi512 : i1.val = 512 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, hbd⟩
      apply List.ext_getElem
      · rw [ints_length512, hidden_mapped_length_probe W l hl]
      · intro k hk' hk''
        rw [ints_length512] at hk'
        have hk512 : k < 512 := by omega
        have hentry := hidden_mapped_entry_probe W l hl (ints r) k hk512
        have hinvk := heq k hk512 (by omega)
        rw [hentry, hinvk]
  · simp only
    refine ⟨by scalar_tac, trivial, repeat_zero_bounded_probe, ?_, ?_⟩
    · intro k hk hik
      exact absurd hik (by show ¬(k < 0); omega)
    · intro k hk hik
      exact repeat_zero_index_probe k hk

end LcnExec.GeneralEngine
