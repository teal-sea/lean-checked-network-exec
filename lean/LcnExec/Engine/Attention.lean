import LcnExec.Engine.Mixing

open Aeneas Aeneas.Std Result ControlFlow
namespace LcnExec.Engine

theorem attention_add_spec (att w : Array I64 128#usize) (b : Int)
    (_hb : 0 ≤ b) (hcap : b + Envelope.head_output ≤ Envelope.attention)
    (ha : Bounded b att) (hw : Bounded Envelope.head_output w) :
    engine.attention_loop0_loop0 att w 0#usize ⦃ r =>
      ints r = TransformerInt.addV (ints att) (ints w) ∧ Bounded (b + Envelope.head_output) r ⦄ := by
  let target := TransformerInt.addV (ints att) (ints w)
  have hlen : target.length = 128 := by simp [target, project_addV_length, ints]
  unfold engine.attention_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (s : Array I64 128#usize × Usize) => 128 - s.2.val)
    (inv := fun (s : Array I64 128#usize × Usize) =>
      s.2.val ≤ 128 ∧ Bounded (b + Envelope.head_output) s.1 ∧
      ∀ (j : Nat) (hj : j < 128),
        (ints s.1)[j]'(by simpa [ints] using hj) =
          if j < s.2.val then target[j]'(by omega) else (ints att)[j]'(by simpa [ints] using hj))
  · rintro ⟨out, k⟩ ⟨hk, hout, heq⟩
    unfold engine.attention_loop0_loop0.body
    dsimp only at hk hout heq ⊢
    simp only [engine.D_MODEL]
    split
    · have hkm : k.val < 128 := by scalar_tac
      step as ⟨wv, hwv⟩
      have hwb := hw wv (by simp [hwv])
      change -1312781500416 ≤ wv.val ∧ wv.val ≤ 1312781500416 at hwb
      change b + 1312781500416 ≤ 5251126001664 at hcap
      step as ⟨av, hav⟩
      have havold : av.val = (ints att)[k.val]'(by simp [ints, hkm]) := by
        simpa [ints, hav] using heq k.val hkm
      have hab := ha (att.val[k.val]'(by simpa using hkm)) (List.getElem_mem (by simpa using hkm))
      have havb : -b ≤ av.val ∧ av.val ≤ b := by simpa [havold, ints] using hab
      step as ⟨v, hv⟩
      step as ⟨out1, hout1⟩
      step as ⟨k1, hk1⟩
      have htarget : v.val = target[k.val]'(by omega) := by
        dsimp [target]
        rw [project_addV_get (ints att) (ints w) (by simp [ints]) k.val (by simp [ints, hkm])]
        simp [hv, havold, ints, hwv]
      simp only [hk1]
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [hout1]
        apply project_bounded_set _ _ _ _ hout
        change -(b+1312781500416) ≤ v.val ∧ v.val ≤ b+1312781500416
        omega
      · intro j hj
        by_cases hjk : j = k.val
        · subst j
          simp [ints, hout1, htarget]
        · have hh : j < k.val + 1 ↔ j < k.val := by omega
          simpa [ints, hout1, Ne.symm hjk, hh] using heq j hj
    · have hkm : k.val = 128 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, hout⟩
      apply List.ext_getElem
      · simpa [ints, target] using hlen.symm
      · intro j hj hj'
        simpa [hkm, show j < 128 by simpa [ints] using hj] using heq j (by simpa [ints] using hj)
  · simp only
    refine ⟨by scalar_tac, ?_, ?_⟩
    · intro v hv
      have hvb := ha v hv
      change -(b+1312781500416) ≤ v.val ∧ v.val ≤ b+1312781500416
      omega
    · intro j hj
      simp

/-- The exact model prefix used by the translated four-head loop. -/
def attention_prefix (W : TransformerInt.Weights) (x0 x1 x2 : List Int) : Nat → List Int
  | 0 => List.replicate 128 0
  | n+1 => TransformerInt.addV (attention_prefix W x0 x1 x2 n) (TransformerInt.headTerm W n x0 x1 x2)

theorem attention_spec_of_stages (hscore : ScoreStage) (hsoft : SoftmaxStage) (hhead : HeadOutputStage)
    (W : engine.Weights) (hW : LoadBounds W)
    (x : Array (Array I64 128#usize) 3#usize) (hx : streams x) :
    engine.attention W x ⦃ r =>
      ints r = TransformerInt.attention (toModel W) (stream x 0) (stream x 1) (stream x 2) ∧
      Bounded Envelope.attention r ⦄ := by
  unfold engine.attention engine.attention_loop0
  apply loop.spec_decr_nat
    (measure := fun (s : Array I64 128#usize × Usize) => 4 - s.2.val)
    (inv := fun (s : Array I64 128#usize × Usize) =>
      s.2.val ≤ 4 ∧ Bounded ((s.2.val : Int) * Envelope.head_output) s.1 ∧
      ints s.1 = attention_prefix (toModel W) (stream x 0) (stream x 1) (stream x 2) s.2.val)
  · rintro ⟨att, h⟩ ⟨hh, hatt, heq⟩
    unfold engine.attention_loop0.body
    dsimp only at hh hatt heq ⊢
    simp only [engine.N_HEADS]
    split
    · have hh4 : h.val < 4 := by scalar_tac
      have hss : engine.head_scores W h x ⦃ s =>
          triple s = TransformerInt.headScores (toModel W) h.val (stream x 0) (stream x 1) (stream x 2) ∧
          Bounded Envelope.score s ⦄ := by
        obtain ⟨s, hs, he, hb⟩ := hscore W hW h x hh4 hx
        simpa [hs] using And.intro he hb
      step with hss as ⟨s, hs, hsb⟩
      have hsm : engine.softmax_weights W s ⦃ a =>
          triple a = TransformerInt.softmaxWeights (toModel W) (triple s) ∧ AlphaBound a ⦄ := by
        obtain ⟨a, ha, he, hb⟩ := hsoft W hW s hsb
        simpa [ha] using And.intro he hb
      step with hsm as ⟨a, ha, hab⟩
      have hho : engine.head_output W h x a ⦃ w =>
          ints w = TransformerInt.headOutput (toModel W) h.val (stream x 0) (stream x 1) (stream x 2) (triple a) ∧
          Bounded Envelope.head_output w ⦄ := by
        obtain ⟨w, hw, he, hb⟩ := hhead W hW h x a hh4 hx hab
        simpa [hw] using And.intro he hb
      step with hho as ⟨w, hw, hwb⟩
      have hnonneg : 0 ≤ (h.val : Int) * Envelope.head_output := by
        change 0 ≤ (h.val : Int) * 1312781500416
        positivity
      have hcap : (h.val : Int) * Envelope.head_output + Envelope.head_output ≤ Envelope.attention := by
        change (h.val : Int) * 1312781500416 + 1312781500416 ≤ 5251126001664
        omega
      step with attention_add_spec att w _ hnonneg hcap hatt hwb as ⟨att1, hatt1, hbatt1⟩
      step as ⟨h1, hh1⟩
      simp only [hh1]
      refine ⟨by omega, ?_, ?_, by omega⟩
      · simpa [Nat.cast_add, Nat.cast_one, add_mul] using hbatt1
      · rw [hatt1, heq, hw, ha, hs]
        rfl
    · have hh4 : h.val = 4 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, ?_⟩
      · simpa [hh4, attention_prefix, TransformerInt.attention] using heq
      · simpa [hh4, Envelope.attention, Envelope.head_output] using hatt
  · simp only
    refine ⟨by scalar_tac, ?_, ?_⟩
    · intro v hv
      have : v = 0#i64 := by simpa using hv
      subst v
      scalar_tac
    · simp only [ints, Array.repeat_val, List.map_replicate]
      rfl

theorem attention_eq_of_stages (hscore : ScoreStage) (hsoft : SoftmaxStage) (hhead : HeadOutputStage) :
    AttentionStage := by
  intro W hW x hx
  have hs := attention_spec_of_stages hscore hsoft hhead W hW x hx
  cases heq : engine.attention W x with
  | ret r => exact ⟨r, rfl, by simpa [heq] using hs⟩
  | vis e k => simp [heq] at hs
  | div => simp [heq] at hs

theorem attention_eq_of_softmax (hsoft : SoftmaxStage) : AttentionStage :=
  attention_eq_of_stages scores_eq hsoft head_output_eq

#print axioms attention_eq_of_softmax
#print axioms attention_add_spec
#print axioms attention_spec_of_stages
#print axioms attention_eq_of_stages
end LcnExec.Engine
