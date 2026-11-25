import LcnExec.GeneralEngine.AttentionPrefix
import LcnExec.GeneralEngine.AttentionAdd
import LcnExec.GeneralEngine.HeadOut

/-!
# The four-head attention loop and entrypoint

`attention_at_loop0` folds `GeneralModel.headTermAt` over `List.range h.val` starting
from the accumulator's value; `attention_at` runs it from the real zero 128-vector.
-/

open Aeneas Aeneas.Std Result ControlFlow

set_option maxHeartbeats 800000

namespace LcnExec.GeneralEngine

theorem att_fold_succ_probe (W : GeneralModel.Weights) (l p h : Nat)
    (xs : List (List Int)) (init : List Int) :
    (List.range (h + 1)).foldl (fun acc j => GeneralModel.addV acc
      (GeneralModel.headTermAt W l j p xs)) init =
    GeneralModel.addV ((List.range h).foldl (fun acc j => GeneralModel.addV acc
      (GeneralModel.headTermAt W l j p xs)) init) (GeneralModel.headTermAt W l h p xs) := by
  rw [List.range_succ, List.foldl_append]
  rfl

theorem att_alpha_nonneg_probe (a : Array I64 32#usize) (p : Usize) (hp : p.val < 32)
    (ha : ∀ v ∈ a.val, 0 ≤ v.val) :
    ∀ j (_ : j ≤ p.val), 0 ≤ (ints a)[j]'(by rw [ints_length32]; omega) := by
  intro j hj
  simp only [ints, List.getElem_map]
  exact ha _ (List.getElem_mem _)

theorem ints_repeat128 : ints (Array.repeat 128#usize 0#i64) = List.replicate 128 (.ofNat 0) := by
  simp [ints, Array.repeat]

theorem attention_loop0_spec (W : general_engine.Weights) (hW : LoadBounds W)
    (l : Usize) (hl : l.val < 2) (x : Array (Array I64 128#usize) 32#usize)
    (p : Usize) (hp : p.val < 32) (hxb : streams x)
    (att : Array I64 128#usize) (hatt : Bounded 0 att) :
    general_engine.attention_at_loop0 W l x p att 0#usize ⦃ r =>
      ints r = (List.range 4).foldl
        (fun acc j => GeneralModel.addV acc
          (GeneralModel.headTermAt (toGeneralModel W) l.val j p.val (ints2 x)))
        (ints att) ∧
      Bounded ((4 : Int) * Envelope.head_output) r ⦄ := by
  unfold general_engine.attention_at_loop0
  apply loop.spec_decr_nat
    (measure := fun (st : Array I64 128#usize × Usize) => 4 - st.2.val)
    (inv := fun (st : Array I64 128#usize × Usize) =>
      st.2.val ≤ 4 ∧
      Bounded ((st.2.val : Int) * Envelope.head_output) st.1 ∧
      ints st.1 = (List.range st.2.val).foldl
        (fun acc j => GeneralModel.addV acc
          (GeneralModel.headTermAt (toGeneralModel W) l.val j p.val (ints2 x)))
        (ints att))
  · rintro ⟨att1, hh⟩ ⟨hh1, hbd, heq⟩
    unfold general_engine.attention_at_loop0.body
    dsimp only at hh1 hbd heq ⊢
    simp only [general_engine.N_HEADS]
    split
    · have hh4 : hh.val < 4 := by scalar_tac
      step with head_scores_at_spec W hW l hh hl hh4 x p hp hxb as ⟨s, hstake, hsbd⟩
      step with softmax_at_spec W hW s p hp hsbd as ⟨alpha, hatake, hapos, hasum⟩
      have halpha := att_alpha_nonneg_probe alpha p hp hapos
      step with head_out_at_spec W hW l hh hl hh4 x p hp hxb alpha halpha hasum as
        ⟨ho, hho, hobd⟩
      have hhead : (0 : Int) ≤ Envelope.head_output := by
        simp only [Envelope.head_output]; norm_num
      have hh3 : (hh.val : Int) ≤ 3 := by omega
      have hb : (hh.val : Int) * Envelope.head_output ≤ 3 * Envelope.head_output :=
        mul_le_mul_of_nonneg_right hh3 hhead
      step with att_add_spec att1 ho (hh.val * Envelope.head_output) hbd hobd hb as
        ⟨att2, hadd, hbd2⟩
      step as ⟨h1, hh1'⟩
      have hhv : h1.val = hh.val + 1 := by scalar_tac
      simp only [hhv]
      have hlen : p.val + 1 ≤ (ints s).length := by
        rw [ints_length32]; omega
      have hn : ∀ j (_ : j ≤ p.val),
          GeneralModel.nth 0 (ints s) j =
          GeneralModel.nth 0 (GeneralModel.headScoresAt (toGeneralModel W) l.val hh.val
            p.val (ints2 x)) j :=
        fun j hj => nth_prefix_probe (ints s) _ p.val hlen hstake j hj
      have hsm : GeneralModel.softmaxAt (toGeneralModel W) (ints s) p.val =
          GeneralModel.softmaxAt (toGeneralModel W)
            (GeneralModel.headScoresAt (toGeneralModel W) l.val hh.val p.val (ints2 x)) p.val :=
        softmax_prefix_probe (toGeneralModel W) (ints s)
          (GeneralModel.headScoresAt (toGeneralModel W) l.val hh.val p.val (ints2 x)) p.val hn
      have hlen2 : p.val + 1 ≤ (ints alpha).length := by
        rw [ints_length32]; omega
      have hn2 : ∀ j (_ : j ≤ p.val),
          GeneralModel.nth 0 (ints alpha) j =
          GeneralModel.nth 0 (GeneralModel.softmaxAt (toGeneralModel W)
            (GeneralModel.headScoresAt (toGeneralModel W) l.val hh.val p.val (ints2 x)) p.val) j :=
        fun j hj => nth_prefix_probe (ints alpha) _ p.val hlen2 (by rw [hatake, hsm]) j hj
      have hho' : ints ho = GeneralModel.headTermAt (toGeneralModel W) l.val hh.val p.val
          (ints2 x) := by
        rw [hho]
        exact head_alpha_prefix_probe (toGeneralModel W) l.val hh.val p.val (ints2 x)
          (ints alpha) _ hn2
      refine ⟨by omega, ?_, ?_, by omega⟩
      · have hkey : ((hh.val : Int) + 1) * Envelope.head_output =
            (hh.val : Int) * Envelope.head_output + Envelope.head_output := by ring
        rw [Nat.cast_add, Nat.cast_one, hkey]
        exact hbd2
      · rw [hadd, hho', heq]
        rw [att_fold_succ_probe (toGeneralModel W) l.val p.val hh.val (ints2 x) (ints att)]
    · have hh4 : hh.val = 4 := by scalar_tac
      simp only [WP.spec_ok]
      rw [hh4] at heq hbd
      exact ⟨heq, hbd⟩
  · simp only
    refine ⟨by scalar_tac, ?_, ?_⟩
    · intro v hv
      have hbb := hatt v hv
      have hz : ((0#usize).val : Int) * Envelope.head_output = 0 := by
        simp
      constructor
      · rw [hz]; exact hbb.1
      · rw [hz]; exact hbb.2
    · simp [List.range_zero, List.foldl_nil]


theorem attention_at_spec (W : general_engine.Weights) (hW : LoadBounds W)
    (l : Usize) (hl : l.val < 2) (x : Array (Array I64 128#usize) 32#usize)
    (p : Usize) (hp : p.val < 32) (hxb : streams x) :
    general_engine.attention_at W l x p ⦃ r =>
      ints r = GeneralModel.attentionAt (toGeneralModel W) l.val p.val (ints2 x) ∧
      Bounded Envelope.attention r ⦄ := by
  have hrep : Bounded 0 (Array.repeat 128#usize 0#i64) := by
    intro v hv
    have hv0 : v.val = 0 := by
      rcases List.mem_replicate.mp (show v ∈ List.replicate 128 0#i64 from by
        simpa [Array.repeat] using hv) with ⟨-, rfl⟩
      rfl
    constructor <;> omega
  unfold general_engine.attention_at
  step with attention_loop0_spec W hW l hl x p hp hxb _ hrep as ⟨r, hfold, hbd⟩
  refine ⟨?_, ?_⟩
  · rw [hfold, ints_repeat128]
    rfl
  · rw [show Envelope.attention = (4 : Int) * Envelope.head_output from by
      simp [Envelope.attention, Envelope.head_output]]
    exact hbd

end LcnExec.GeneralEngine
