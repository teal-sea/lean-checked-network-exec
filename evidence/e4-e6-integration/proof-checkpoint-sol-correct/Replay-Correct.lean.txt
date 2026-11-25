import LcnExec.GeneralEngine.Load
import LcnExec.GeneralEngine.ForwardInputs
import LcnExec.GeneralEngine.ForwardStack
import LcnExec.GeneralEngine.Unembed
import LcnExec.GeneralEngine.Argmax

set_option maxHeartbeats 800000

open Aeneas Aeneas.Std Result

namespace LcnExec.GeneralEngine

private theorem result_witness {α : Type} {m : Result α} {P : α → Prop}
    (h : m ⦃ r => P r ⦄) : ∃ r, m = ok r ∧ P r := by
  cases heq : m with
  | ret r => exact ⟨r, rfl, by simpa [heq] using h⟩
  | vis e k => simp [heq] at h
  | div => simp [heq] at h

private theorem accepted_sizes (W : general_engine.Weights)
    (hload : general_engine.load_check W = ok true) :
    0 < W.n_layers.val ∧ W.n_layers.val ≤ 2 ∧
      0 < W.vocab_size.val ∧ W.vocab_size.val ≤ 256 := by
  let scalar : Result Bool :=
    if W.n_layers >= 1#usize then
      if W.n_layers <= general_engine.MAX_LAYERS then
        if W.vocab_size >= 1#usize then ok (decide (W.vocab_size <= general_engine.VOCAB))
        else ok false
      else ok false
    else ok false
  have hscalar : scalar ⦃ b => scalar = ok b ⦄ := by
    obtain ⟨b, hb, _⟩ :=
      result_witness (show scalar ⦃ _ => True ⦄ from load_scalars_spec W)
    simp only [hb, WP.spec_ok]
  have hretains : general_engine.load_check W ⦃ b => b = true → scalar = ok true ⦄ := by
    unfold general_engine.load_check
    refine WP.spec_bind hscalar ?_
    intro valid hvalid
    step as ⟨valid1, hvalid1⟩
    step as ⟨valid2, hvalid2⟩
    step as ⟨valid3, hvalid3⟩
    step as ⟨valid4, hvalid4⟩
    split
    · rename_i hchecked
      have h3 := (hvalid4 hchecked).1
      have h2 := (hvalid3 h3).1
      have h1 := (hvalid2 h2).1
      have h0 := (hvalid1 h1).1
      have hscalarTrue : scalar = ok true := by simpa only [h0] using hvalid
      step as ⟨bn, hbn⟩
      split
      · step as ⟨b2, hb2⟩
        split
        · step as ⟨b1, hb1⟩
          split
          · step as ⟨b0, hb0⟩
            exact hscalarTrue
          · simp
        · simp
      · simp
    · simp
  have hscalarTrue : scalar = ok true := by simpa [hload] using hretains
  dsimp only [scalar] at hscalarTrue
  split at hscalarTrue
  · rename_i hnmin
    split at hscalarTrue
    · rename_i hnmax
      split at hscalarTrue
      · rename_i hvmin
        have hvmax : W.vocab_size ≤ general_engine.VOCAB :=
          of_decide_eq_true (Result.ok_injective hscalarTrue)
        simp only [general_engine.MAX_LAYERS] at hnmax
        simp only [general_engine.VOCAB] at hvmax
        exact ⟨by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac⟩
      · simp at hscalarTrue
    · simp at hscalarTrue
  · simp at hscalarTrue

private theorem initial_row_model :
    ints (Array.repeat 128#usize 0#i64) = GeneralModel.zeroRow := by
  have h128 : (128#usize).val = (128 : Nat) := by scalar_tac
  have h0 : (0#i64).val = (0 : Int) := by scalar_tac
  simp only [ints, repeat_val_probe, List.map_replicate, h128, h0, GeneralModel.zeroRow]
  rfl

private theorem initial_row_bounded :
    Bounded Envelope.final_stream (Array.repeat 128#usize 0#i64) := by
  intro v hv
  rw [repeat_val_probe] at hv
  have hzero : v = 0#i64 := (List.mem_replicate.mp hv).2
  rw [hzero]
  constructor <;> simp only [Envelope.final_stream] <;> norm_num

private def forwardResult (W : GeneralModel.Weights) (tokens : List Nat) (n : Nat) :
    Option (List Int) :=
  if n = 0 ∨ n > 32 then none
  else if (tokens.take n).any (fun t => t ≥ 256) then none
  else some (GeneralModel.forwardLogits W tokens n)

/-- Total correctness of the guarded forward pass on every load-accepted input.
The successful case preserves the ordered vector of all 256 logits. -/
theorem forward_logits_spec (W : general_engine.Weights)
    (hload : general_engine.load_check W = ok true)
    (tokens : Array Usize 32#usize) (seq_len : Usize) :
    general_engine.forward_logits W tokens seq_len ⦃ out =>
      out.map ints =
        if seq_len.val = 0 ∨ seq_len.val > 32 then none
        else if ((tokens.val.map (·.val)).take seq_len.val).any (fun t => t ≥ 256) then none
        else some (GeneralModel.forwardLogits (toGeneralModel W)
          (tokens.val.map (·.val)) seq_len.val) ⦄ := by
  change general_engine.forward_logits W tokens seq_len ⦃ out =>
    out.map ints = forwardResult (toGeneralModel W) (tokens.val.map (·.val)) seq_len.val ⦄
  have hW := load_sound W hload
  obtain ⟨hnpos, hn, hvpos, hv⟩ := accepted_sizes W hload
  have hmodelLayers : (toGeneralModel W).nLayers = W.n_layers.val := rfl
  unfold general_engine.forward_logits
  simp only [general_engine.MAX_SEQ, general_engine.MAX_LAYERS, general_engine.VOCAB]
  split
  · have hz : seq_len.val = 0 := by scalar_tac
    simp [forwardResult, hz]
  · have hspos : 0 < seq_len.val := by scalar_tac
    split
    · have hlong : seq_len.val > 32 := by scalar_tac
      simp [forwardResult, hlong]
    · have hs : seq_len.val ≤ 32 := by scalar_tac
      have hnz : W.n_layers ≠ 0#usize := by scalar_tac
      have hnl : ¬ W.n_layers > 2#usize := by scalar_tac
      have hvz : W.vocab_size ≠ 0#usize := by scalar_tac
      have hvl : ¬ W.vocab_size > 256#usize := by scalar_tac
      have hseq : ¬ (seq_len.val = 0 ∨ seq_len.val > 32) := by omega
      simp only [ite_eq_right hnz, ite_eq_right hnl, ite_eq_right hvz, ite_eq_right hvl]
      refine WP.spec_bind (forward_logits_loop0_spec tokens seq_len hs) ?_
      intro b hcheck
      have hbridge := tokens_invalid_eq_false_iff tokens seq_len.val hs
      split
      · rename_i hb
        have hvalid : ValidTokenPrefix tokens seq_len.val := hcheck.mp hb
        have hmodelValid := hbridge.mpr hvalid
        step with embed_all_spec W hW tokens seq_len hs hvalid as ⟨x, hxmodel, hx⟩
        step with forward_logits_loop1_spec W hW seq_len hspos hs hn x hx
          (Array.repeat 128#usize 0#i64) initial_row_bounded as ⟨last, hlastmodel, hlast⟩
        step with unembed_spec W hW last hlast as ⟨logits, hlogits, hlogitBounds⟩
        simp only [Option.map_some]
        rw [hlogits, hlastmodel, hxmodel, initial_row_model]
        simp [forwardResult, hseq, hmodelValid, GeneralModel.forwardLogits, hmodelLayers]
      · rename_i hb
        have hmodelInvalid :
            ((tokens.val.map (·.val)).take seq_len.val).any (fun t => t ≥ 256) = true := by
          apply Bool.ne_false_iff.mp
          intro hfalse
          exact hb (hcheck.mpr (hbridge.mp hfalse))
        simp [forwardResult, hseq, hmodelInvalid]

theorem predict_next_spec (W : general_engine.Weights)
    (hload : general_engine.load_check W = ok true)
    (tokens : Array Usize 32#usize) (seq_len : Usize) :
    general_engine.predict_next W tokens seq_len ⦃ out =>
      out.map (·.val) =
        GeneralModel.predictNext (toGeneralModel W) (tokens.val.map (·.val)) seq_len.val ⦄ := by
  obtain ⟨hnpos, hn, hvpos, hv⟩ := accepted_sizes W hload
  have hmodelLayers : ¬ ((toGeneralModel W).nLayers = 0 ∨ (toGeneralModel W).nLayers > 2) := by
    change ¬ (W.n_layers.val = 0 ∨ W.n_layers.val > 2)
    omega
  have hmodelVocab : ¬ ((toGeneralModel W).vocabSize = 0 ∨ (toGeneralModel W).vocabSize > 256) := by
    change ¬ (W.vocab_size.val = 0 ∨ W.vocab_size.val > 256)
    omega
  have hmodelVocabVal : (toGeneralModel W).vocabSize = W.vocab_size.val := rfl
  have hmodel : GeneralModel.predictNext (toGeneralModel W) (tokens.val.map (·.val)) seq_len.val =
      (forwardResult (toGeneralModel W) (tokens.val.map (·.val)) seq_len.val).map
        (fun scores => GeneralModel.argmaxN scores W.vocab_size.val) := by
    by_cases hseq : seq_len.val = 0 ∨ seq_len.val > 32
    · simp [GeneralModel.predictNext, forwardResult, hseq]
    · by_cases ht : ((tokens.val.map (·.val)).take seq_len.val).any (fun t => t ≥ 256) = true
      · simp [GeneralModel.predictNext, forwardResult, hseq, hmodelLayers, hmodelVocab, ht]
      · simp [GeneralModel.predictNext, forwardResult, hseq, hmodelLayers, ht,
          hmodelVocabVal, Nat.ne_of_gt hvpos, hv]
  unfold general_engine.predict_next
  refine WP.spec_bind (forward_logits_spec W hload tokens seq_len) ?_
  intro logits hlogits
  change logits.map ints =
    forwardResult (toGeneralModel W) (tokens.val.map (·.val)) seq_len.val at hlogits
  rw [hmodel, ← hlogits]
  cases logits with
  | none => simp
  | some l =>
    step with argmax_spec l W.vocab_size hvpos hv as ⟨r, hr, hrbound⟩
    simp only [Option.map_some, hr]

/-- The return value exists for every sequence at every load-accepted weight set,
and the option agrees exactly with the frozen model. -/
def GeneralEngineCorrect : Prop :=
  ∀ (W : general_engine.Weights), general_engine.load_check W = ok true →
    ∀ (tokens : Array Usize 32#usize) (seq_len : Usize),
      ∃ out : Option Usize, general_engine.predict_next W tokens seq_len = Result.ok out ∧
        out.map (·.val) =
          GeneralModel.predictNext (toGeneralModel W) (tokens.val.map (·.val)) seq_len.val

theorem general_engine_correct : GeneralEngineCorrect := by
  intro W hload tokens seq_len
  exact result_witness (predict_next_spec W hload tokens seq_len)

end LcnExec.GeneralEngine
