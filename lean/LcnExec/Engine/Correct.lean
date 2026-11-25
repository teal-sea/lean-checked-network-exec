import LcnExec.Engine.Load
import LcnExec.Engine.Softmax
import LcnExec.Engine.Attention
import LcnExec.Engine.Argmax

open Aeneas Aeneas.Std Result
namespace LcnExec.Engine

/-- Every attention hypothesis is now discharged by the actual stage proofs. -/
theorem attention_eq : AttentionStage := attention_eq_of_softmax softmax_eq

/-- The complete translated forward function equals the unchanged integer model. -/
theorem forward_eq : ForwardStage := by
  intro W hload a b ha hb
  have hW := load_sound W hload
  obtain ⟨x0, hx0, he0, hb0⟩ := embed_eq W hW a 0#usize (by omega) (by scalar_tac)
  obtain ⟨x1, hx1, he1, hb1⟩ := embed_eq W hW b 1#usize (by omega) (by scalar_tac)
  obtain ⟨x2, hx2, he2, hb2⟩ := embed_eq W hW engine.EQ 2#usize (by simp [engine.EQ]) (by scalar_tac)
  let x : Array (Array I64 128#usize) 3#usize := Array.make 3#usize [x0, x1, x2]
  have hxs : streams x := by
    intro row hrow
    have hrow' : row = x0 ∨ row = x1 ∨ row = x2 := by simpa [x] using hrow
    rcases hrow' with rfl | rfl | rfl
    · exact hb0
    · exact hb1
    · exact hb2
  have hs0 : stream x 0 = ints x0 := rfl
  have hs1 : stream x 1 = ints x1 := rfl
  have hs2 : stream x 2 = ints x2 := rfl
  obtain ⟨att, hatt, heatt, hbatt⟩ := attention_eq W hW x hxs
  obtain ⟨r, hr, her, hbr⟩ := residual_eq x2 att hb2 hbatt
  obtain ⟨m, hm, hem, hbm, _⟩ := mlp_hidden_eq W hW r hbr
  obtain ⟨o, ho, heo, hbo⟩ := mlp_output_eq W hW m hbm
  obtain ⟨f, hf, hef, hbf⟩ := final_eq r o hbr hbo
  obtain ⟨l, hl, hel, _⟩ := unembed_eq W hW f hbf
  refine ⟨l, ?_, ?_⟩
  · have hindex : Array.index_usize x 2#usize = ok x2 := by
      simp [x, Array.index_usize, Array.make]
    simp [x] at hatt hindex
    simp [engine.forward, hx0, hx1, hx2, hatt, hindex, hr, hm, ho, hf, hl]
  · rw [hel, hef, heo, hem, her, heatt, hs0, hs1, hs2, he0, he1, he2]
    simp [TransformerInt.forward, TransformerInt.EQ, engine.EQ]

/-- Total correctness for every load accepted by the translated Rust checker.
No fixed trained weights, enumeration, or gate 4 premise enters this theorem. -/
theorem engine_correct : EngineCorrect := by
  intro W hW a b ha hb
  obtain ⟨l, hl, hel⟩ := forward_eq W hW a b ha hb
  obtain ⟨r, hr, her, _⟩ := argmax_eq l
  refine ⟨r, ?_, ?_⟩
  · have hna : ¬ a ≥ engine.P := by simp only [engine.P]; scalar_tac
    have hnb : ¬ b ≥ engine.P := by simp only [engine.P]; scalar_tac
    simp [engine.predict, hna, hnb, hl, hr]
  · have hn : ¬ (a.val ≥ TransformerInt.P ∨ b.val ≥ TransformerInt.P) := by
      simp only [TransformerInt.P]
      omega
    simp only [TransformerInt.predict, ite_eq_right hn, ← hel, ← her]

#print axioms attention_eq
#print axioms forward_eq
#print axioms engine_correct
end LcnExec.Engine
