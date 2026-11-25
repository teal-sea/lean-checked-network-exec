import LcnExec.GeneralEngine.ProjectionInner

/-!
# The outer 128-coordinate projection scan `general_engine.head_out_at_loop2`

Coordinate `k < 128` of the head output is the inner dot against the `wo` column; the
scan threads the weights unchanged and yields the exact `GeneralModel.lincomb 128`
over the model WO matrix, bounded by `Envelope.head_output`.
-/

open Aeneas Aeneas.Std Result ControlFlow

set_option maxHeartbeats 800000

namespace LcnExec.GeneralEngine

theorem ints_length128 (o : Array I64 128#usize) : (ints o).length = 128 := by
  simp [ints]

/-- The model WO matrix of head `h` as `List (List Int)` rows, via the `!`-lookup. -/
def woRows (w : general_engine.Weights) (l h : Nat) : List (List Int) :=
  ((w.layers.val[l]!).wo.val[h]!).val.map (fun row => row.val.map (·.val))

theorem woRows_length (w : general_engine.Weights) (l h : Nat) :
    (woRows w l h).length = 32 := by
  simp [woRows]

theorem rows_map_bridge (rows : List (Array I8 128#usize)) (k : Nat) (hk : k < 128) :
    rows.map (fun r => (r.val[k]!).val) =
      (rows.map (fun r => r.val.map (·.val))).map (fun r => GeneralModel.nth 0 r k) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons]
    congr 1
    · rw [project_nth_eq 0 (r.val.map (·.val)) k
        (by rw [List.length_map, Array.length_eq]; exact hk)]
      simp only [List.getElem_map]
      rw [getElem!_pos _ k (by rw [Array.length_eq]; exact hk)]

theorem woRows_row_length (w : general_engine.Weights) (l h : Nat)
    (row : List Int) (hrow : row ∈ woRows w l h) : row.length = 128 := by
  rcases List.mem_map.mp (by simpa [woRows] using hrow) with ⟨r, _, rfl⟩
  simp

/-- The model-side WO matrix of head `h` equals the runtime rows. -/
theorem woRows_eq (W : general_engine.Weights) (l h : Usize) (hl : l.val < 2)
    (hh : h.val < 4) :
    GeneralModel.nth [] (GeneralModel.layer (toGeneralModel W) l.val).wo h.val =
      woRows W l.val h.val := by
  rw [model_layer_eq W l hl]
  rw [project_nth_eq _ _ _
    (by simp [toLayerModel, List.length_map]; omega)]
  simp only [toLayerModel, List.getElem_map, woRows]
  rw [getElem!_pos _ l.val (by simp; omega), getElem!_pos _ h.val (by simp; omega)]

/-- Column bridge: the projection column equals the lincomb column at `k < 128`. -/
theorem woColumn_eq (W : general_engine.Weights) (l h : Nat) (k : Nat) (hk : k < 128) :
    woColumn W l h k =
      (woRows W l h).map (fun row => GeneralModel.nth 0 row k) := by
  exact rows_map_bridge (((W.layers.val[l]!).wo.val[h]!).val) k hk

theorem proj_scan_spec (W : general_engine.Weights) (hW : LoadBounds W)
    (l h : Usize) (hl : l.val < 2) (hh : h.val < 4)
    (z : Array I64 32#usize) (hz : Bounded Envelope.mixed_value z) :
    general_engine.head_out_at_loop2 W l h z
      (Array.repeat 128#usize 0#i64) 0#usize ⦃ r =>
      ints r = GeneralModel.lincomb 128 (ints z) (woRows W l.val h.val) ∧
      Bounded Envelope.head_output r ⦄ := by
  have hrowl : ∀ row ∈ woRows W l.val h.val, row.length = 128 :=
    woRows_row_length W l.val h.val
  unfold general_engine.head_out_at_loop2
  apply loop.spec_decr_nat
    (measure := fun (st : general_engine.Weights × Array I64 128#usize × Usize) => 128 - st.2.2.val)
    (inv := fun (st : general_engine.Weights × Array I64 128#usize × Usize) =>
      st.2.2.val ≤ 128 ∧
      st.1 = W ∧
      Bounded Envelope.head_output st.2.1 ∧
      ∀ (k' : Nat) (hk' : k' < 128) (hik : k' < st.2.2.val),
        (ints st.2.1)[k']'(by rw [ints_length128]; omega) =
          GeneralModel.dot (ints z) (woColumn W l.val h.val k'))
  · rintro ⟨w1, out, k⟩ ⟨hk1, hw, hbd, heq⟩
    unfold general_engine.head_out_at_loop2.body
    dsimp only at hk1 hw hbd heq ⊢
    simp only [general_engine.D_MODEL]
    split
    · have hk128 : k.val < 128 := by scalar_tac
      have hwL : LoadBounds w1 := by rw [hw]; exact hW
      step with head_out_proj_inner_spec w1 hwL l h hl hh z hz k hk128 as
        ⟨w1', acc, hw1', haccv, hblo, hbhi⟩
      step with Array.update_spec out k acc (by simp; omega) as ⟨a, ha⟩
      step as ⟨k1, hk1'⟩
      simp only [hk1']
      refine ⟨by omega, by rw [hw1', hw], ?_, ?_, by omega⟩
      · rw [ha]
        exact project_bounded_set _ _ _ _ hbd ⟨hblo, hbhi⟩
      · intro k' hk' hik
        by_cases hkk : k' = k.val
        · subst k'
          have hval : (ints a)[k.val]'(by rw [ints_length128]; omega) = acc.val := by
            rw [ha]
            simp only [ints, Array.set_val_eq, List.getElem_map]
            rw [List.getElem_set_self (by simp; omega)]
          rw [hw] at haccv
          rw [hval, haccv]
        · have hval : (ints a)[k']'(by rw [ints_length128]; omega) =
              (ints out)[k']'(by rw [ints_length128]; omega) := by
            simp only [ha, ints, Array.set_val_eq, List.getElem_map]
            rw [List.getElem_set_ne (by omega)]
          rw [hval]
          exact heq k' hk' (by omega)
    · have hk128 : k.val = 128 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, hbd⟩
      apply List.ext_getElem
      · rw [ints_length128, project_lincomb_length 128 (ints z) (woRows W l.val h.val) hrowl]
      · intro k' hk' hk''
        have hk'128 : k' < 128 := by rw [ints_length128] at hk'; omega
        have hinv := heq k' hk'128 (by omega)
        have hlc := project_lincomb_get 128 (ints z) (woRows W l.val h.val) hrowl k'
          (by omega)
        rw [woColumn_eq W l.val h.val k' hk'128] at hinv
        rw [hlc]
        exact hinv
  · simp only
    refine ⟨by scalar_tac, trivial, ?_, ?_⟩
    · intro v hv
      have hvz : v = 0#i64 := by simpa using hv
      subst hvz
      constructor <;> (simp only [Envelope.head_output]; norm_num)
    · intro k' hk' hik
      exact absurd hik (by show ¬(k' < 0); omega)

end LcnExec.GeneralEngine
