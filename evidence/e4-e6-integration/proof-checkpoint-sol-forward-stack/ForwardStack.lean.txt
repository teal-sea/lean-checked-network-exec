import LcnExec.GeneralEngine.RescaleClamp

set_option maxHeartbeats 800000

open Aeneas Aeneas.Std Result ControlFlow

namespace LcnExec.GeneralEngine

/-- Execute the active layers from cursor zero, carrying the unclamped final row. -/
theorem forward_logits_loop1_spec (W : general_engine.Weights) (hW : LoadBounds W)
    (seq_len : Usize) (hspos : 0 < seq_len.val) (hs : seq_len.val ≤ 32)
    (hn : W.n_layers.val ≤ 2)
    (x : Array (Array I64 128#usize) 32#usize) (hx : streams x)
    (last : Array I64 128#usize) (hlast : Bounded Envelope.final_stream last) :
    general_engine.forward_logits_loop1 W.n_layers W.vocab_size W.tok W.pos
        W.layers W.u W.exp_n W.exp_2 W.exp_1 W.exp_0
        seq_len x last 0#usize ⦃ out =>
      ints out = GeneralModel.runLayers (toGeneralModel W) 0 W.n_layers.val
        (ints2 x) seq_len.val (ints last) ∧
      Bounded Envelope.final_stream out ⦄ := by
  let initialModelResult := GeneralModel.runLayers (toGeneralModel W) 0 W.n_layers.val
    (ints2 x) seq_len.val (ints last)
  have hweights : ({
      n_layers := W.n_layers
      vocab_size := W.vocab_size
      tok := W.tok
      pos := W.pos
      layers := W.layers
      u := W.u
      exp_n := W.exp_n
      exp_2 := W.exp_2
      exp_1 := W.exp_1
      exp_0 := W.exp_0
    } : general_engine.Weights) = W := by
    cases W
    rfl
  have hmodelLayers : (toGeneralModel W).nLayers = W.n_layers.val := rfl
  unfold general_engine.forward_logits_loop1
  apply loop.spec_decr_nat
    (measure := fun (st : Array (Array I64 128#usize) 32#usize × Array I64 128#usize × Usize) =>
      W.n_layers.val - st.2.2.val)
    (inv := fun (st : Array (Array I64 128#usize) 32#usize × Array I64 128#usize × Usize) =>
      st.2.2.val ≤ W.n_layers.val ∧
      streams st.1 ∧
      Bounded Envelope.final_stream st.2.1 ∧
      GeneralModel.runLayers (toGeneralModel W) st.2.2.val (W.n_layers.val - st.2.2.val)
        (ints2 st.1) seq_len.val (ints st.2.1) = initialModelResult)
  · rintro ⟨current, saved, l⟩ ⟨hl, hcurrent, hsaved, heq⟩
    unfold general_engine.forward_logits_loop1.body
    dsimp only at hl hcurrent hsaved heq ⊢
    split
    · have hlt : l.val < W.n_layers.val := by scalar_tac
      have hl2 : l.val < 2 := by omega
      try rw [hweights]
      step with layer_forward_spec W hW l hl2 current hcurrent seq_len hs as ⟨f, hfeq, hfb⟩
      step as ⟨l1, hl1⟩
      have hl1v : l1.val = l.val + 1 := by scalar_tac
      have hremain : W.n_layers.val - l.val = (W.n_layers.val - (l.val + 1)).succ := by omega
      rw [hremain] at heq
      simp only [GeneralModel.runLayers, hmodelLayers, ← hfeq] at heq
      by_cases hmore : l1 < W.n_layers
      · rw [ite_eq_left hmore]
        have hmoreVal : l.val + 1 < W.n_layers.val := by
          have h : l1.val < W.n_layers.val := by scalar_tac
          omega
        rw [ite_eq_left hmoreVal] at heq
        step with rescale_clamp_spec f hfb as ⟨scaled, hscaled, hscaledBound⟩
        simp only [hl1v]
        refine ⟨by omega, hscaledBound, hsaved, ?_, by omega⟩
        rw [hscaled]
        exact heq
      · rw [ite_eq_right hmore]
        have hlastVal : ¬ l.val + 1 < W.n_layers.val := by
          have h : ¬ l1.val < W.n_layers.val := by scalar_tac
          omega
        rw [ite_eq_right hlastVal] at heq
        have hsone : (1#usize).val ≤ seq_len.val := by scalar_tac
        step as ⟨p, hp⟩
        have hpv : p.val = seq_len.val - 1 := by scalar_tac
        have hp32 : p.val < 32 := by omega
        have hrowBound : Bounded Envelope.final_stream (f.val[p.val]'(by simpa using hp32)) :=
          hfb _ (List.getElem_mem _)
        step with row_at_spec f p hp32 Envelope.final_stream
          (by norm_num [Envelope.final_stream]) hrowBound as ⟨row, hroweq, hrowbd⟩
        simp only [hl1v]
        refine ⟨by omega, hcurrent, hrowbd, ?_, by omega⟩
        rw [hroweq, hpv]
        exact heq
    · have hlEnd : l.val = W.n_layers.val := by scalar_tac
      have hzero : W.n_layers.val - l.val = 0 := by omega
      simp only [WP.spec_ok]
      refine ⟨?_, hsaved⟩
      simpa only [hzero, GeneralModel.runLayers] using heq
  · refine ⟨by scalar_tac, hx, hlast, ?_⟩
    change GeneralModel.runLayers (toGeneralModel W) 0 (W.n_layers.val - 0)
      (ints2 x) seq_len.val (ints last) = initialModelResult
    simp only [Nat.sub_zero, initialModelResult]

end LcnExec.GeneralEngine
