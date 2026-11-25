import LcnExec.GeneralEngine.ProjectionScan
import LcnExec.GeneralEngine.MixScan
import LcnExec.GeneralEngine.ValueScan

/-!
# Composed `head_out_at`: exact `GeneralModel.headOutAt` and `Bounded Envelope.head_output`.
-/

open Aeneas Aeneas Std Result ControlFlow

set_option maxHeartbeats 800000

namespace LcnExec.GeneralEngine

private theorem foldl_congr' {α γ} (f g : γ → α → γ) (l : List α) (init : γ)
    (h : ∀ (a : α) (acc : γ), a ∈ l → f acc a = g acc a) :
    l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons a rest ih =>
    rw [List.foldl_cons, List.foldl_cons, h a init (by simp)]
    exact ih (g init a) (fun a' acc ha' => h a' acc (by simp [ha']))

/-- `mixAt` only reads `rowAt vs j` for `j <= p`. -/
theorem mixAt_congr (alpha : List Int) (vs vs' : List (List Int)) (p : Nat)
    (h : ∀ j (_ : j ≤ p), GeneralModel.rowAt vs j = GeneralModel.rowAt vs' j) :
    GeneralModel.mixAt alpha vs p = GeneralModel.mixAt alpha vs' p := by
  unfold GeneralModel.mixAt
  congr 1
  funext i
  congr 1
  apply foldl_congr'
  intro j acc hj
  rw [h j (by simpa using hj)]

theorem head_out_at_spec (W : general_engine.Weights) (hW : LoadBounds W)
    (l h : Usize) (hl : l.val < 2) (hh : h.val < 4)
    (x : Array (Array I64 128#usize) 32#usize) (p : Usize) (hp : p.val < 32)
    (hxb : streams x)
    (alpha : Array I64 32#usize)
    (halpha : ∀ j (_ : j ≤ p.val), 0 ≤ (ints alpha)[j]'(by rw [ints_length32]; omega))
    (hsum : ((ints alpha).take (p.val + 1)).sum ≤ 16777216) :
    general_engine.head_out_at W l h x p alpha ⦃ r =>
      ints r = GeneralModel.headOutAt (toGeneralModel W) l.val h.val p.val (ints2 x)
        (ints alpha) ∧
      Bounded Envelope.head_output r ⦄ := by
  unfold general_engine.head_out_at
  step with value_scan_weights_spec W hW l h hl hh x p hp hxb as
    ⟨w1, vs1, hw1, hpref, hvsb⟩
  step with mix_scan_spec p hp alpha vs1 halpha hsum hvsb as ⟨z1, hmix, hzbd⟩
  have hwL : LoadBounds w1 := by rw [hw1]; exact hW
  step with proj_scan_spec w1 hwL l h hl hh z1 hzbd as ⟨out, hout, houtbd⟩
  refine ⟨?_, houtbd⟩
  rw [hout, hmix, hw1]
  -- goal: lincomb 128 (mixAt (ints alpha) (vals2 vs1) p) (woRows W l h)
  --     = headOutAt (toGeneralModel W) l h p (ints2 x) (ints alpha)
  have hrowj : ∀ j (_ : j ≤ p.val),
      GeneralModel.rowAt (vals2 vs1) j =
      GeneralModel.rowAt ((List.range (p.val + 1)).map
        (fun j => GeneralModel.value (toGeneralModel W) l.val h.val
          (GeneralModel.rowAt (ints2 x) j))) j := by
    intro j hj
    have hl1 : (vals2 vs1).length = 32 := vals2_length vs1
    have hn : GeneralModel.rowAt (vals2 vs1) j =
        ((vals2 vs1).take (p.val + 1))[j]'(by rw [List.length_take, hl1]; omega) := by
      unfold GeneralModel.rowAt
      rw [project_nth_eq _ _ _ (by rw [hl1]; omega)]
      exact List.getElem_take' (xs := vals2 vs1) (i := j) (j := p.val + 1)
        (by rw [hl1]; omega) (by omega)
    have hval : ((vals2 vs1).take (p.val + 1))[j]'(by rw [List.length_take, hl1]; omega) =
        GeneralModel.value (toGeneralModel W) l.val h.val
          (GeneralModel.rowAt (ints2 x) j) := by
      simp only [hpref, List.getElem_map,
        List.getElem_range (show j < (List.range (p.val + 1)).length by simp; omega)]
    have hval2 : GeneralModel.rowAt ((List.range (p.val + 1)).map
        (fun j => GeneralModel.value (toGeneralModel W) l.val h.val
          (GeneralModel.rowAt (ints2 x) j))) j =
        GeneralModel.value (toGeneralModel W) l.val h.val
          (GeneralModel.rowAt (ints2 x) j) := by
      unfold GeneralModel.rowAt
      rw [project_nth_eq _ _ _ (by simp; omega)]
      simp [List.getElem_map,
        List.getElem_range (show j < (List.range (p.val + 1)).length by simp; omega)]
    exact (hn.trans hval).trans hval2.symm
  rw [← woRows_eq W l h hl hh]
  show GeneralModel.lincomb 128 (GeneralModel.mixAt (ints alpha) (vals2 vs1) p.val)
      (GeneralModel.nth [] (GeneralModel.layer (toGeneralModel W) l.val).wo h.val) =
    GeneralModel.lincomb 128 (GeneralModel.mixAt (ints alpha)
      ((List.range (p.val + 1)).map (fun j => GeneralModel.value (toGeneralModel W) l.val h.val
        (GeneralModel.rowAt (ints2 x) j))) p.val)
      (GeneralModel.nth [] (GeneralModel.layer (toGeneralModel W) l.val).wo h.val)
  rw [mixAt_congr (ints alpha) (vals2 vs1)
    ((List.range (p.val + 1)).map
      (fun j => GeneralModel.value (toGeneralModel W) l.val h.val
        (GeneralModel.rowAt (ints2 x) j))) p.val hrowj]

end LcnExec.GeneralEngine
