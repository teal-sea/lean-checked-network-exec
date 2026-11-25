import LcnExec.Engine.Projection

open Aeneas Aeneas.Std Result ControlFlow
namespace LcnExec.Engine

theorem downstream_residual_length (xs ys : List Int) (h : xs.length = ys.length) :
    (TransformerInt.residual xs ys).length = xs.length := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys => simpa [TransformerInt.residual] using ih ys (by simpa using h)

theorem downstream_residual_get (xs ys : List Int) (h : xs.length = ys.length)
    (i : Nat) (hi : i < xs.length) :
    (TransformerInt.residual xs ys)[i]'(by rw [downstream_residual_length xs ys h]; exact hi) =
      xs[i] * 16777216 + ys[i]'(by omega) := by
  induction xs generalizing ys i with
  | nil => simp at hi
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i => exact ih ys (by simpa using h) i (by simpa using hi)

theorem residual_spec (x a : Array I64 128#usize)
    (hx : Bounded Envelope.embedding x) (ha : Bounded Envelope.attention a) :
    engine.residual x a ⦃ r => ints r = TransformerInt.residual (ints x) (ints a) ∧
      Bounded Envelope.residual r ⦄ := by
  unfold engine.residual engine.residual_loop
  apply loop.spec_decr_nat
    (measure := fun (s : Array I64 128#usize × Usize) => 128 - s.2.val)
    (inv := fun (s : Array I64 128#usize × Usize) =>
      s.2.val ≤ 128 ∧ Bounded Envelope.residual s.1 ∧
      ∀ (j : Nat) (hj : j < 128), j < s.2.val →
        (ints s.1)[j]'(by simpa [ints] using hj) =
          (ints x)[j]'(by simpa [ints] using hj) * 16777216 +
          (ints a)[j]'(by simpa [ints] using hj))
  · rintro ⟨out, k⟩ ⟨hk, hout, heq⟩
    unfold engine.residual_loop.body
    dsimp only at hk hout heq ⊢
    simp only [engine.D_MODEL]
    split
    · have hk128 : k.val < 128 := by scalar_tac
      step as ⟨xv, hxv⟩
      have hxb := hx xv (by simp [hxv])
      change -127 ≤ xv.val ∧ xv.val ≤ 127 at hxb
      simp only [engine.ALPHA_ONE]
      step as ⟨c, hc⟩
      have hc' : c.val = 16777216 := by
        have hnum : (1 <<< 24 : Int).bmod I64.size = 16777216 := by
          norm_num [Int.shiftLeft_eq, I64.size, I64.numBits, Int.bmod]
        exact hc.trans hnum
      step as ⟨p, hp⟩
      step as ⟨av, hav⟩
      have hab := ha av (by simp [hav])
      change -5251126001664 ≤ av.val ∧ av.val ≤ 5251126001664 at hab
      step as ⟨v, hv⟩
      step as ⟨out1, hout1⟩
      step as ⟨k1, hk1⟩
      have hvsum : v.val = xv.val * 16777216 + av.val := by scalar_tac
      simp only [hk1]
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [hout1]
        apply project_bounded_set _ _ _ _ hout
        change -5253256708096 ≤ v.val ∧ v.val ≤ 5253256708096
        omega
      · intro j hj hjk
        by_cases hjk' : j = k.val
        · subst j
          simpa [ints, hout1, hxv, hav] using hvsum
        · have hjold : j < k.val := by omega
          simpa [ints, hout1, Ne.symm hjk'] using heq j hj hjold
    · have hk128 : k.val = 128 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, hout⟩
      apply List.ext_getElem
      · simp [ints, downstream_residual_length]
      · intro j hj hj'
        rw [downstream_residual_get (ints x) (ints a) (by simp [ints]) j (by simpa [ints] using hj)]
        exact heq j (by simpa [ints] using hj) (by simpa [ints, hk128] using hj)
  · simp only
    refine ⟨by scalar_tac, ?_, ?_⟩
    · intro v hv
      have : v = 0#i64 := by simpa using hv
      subst v
      change -5253256708096 ≤ (0#i64).val ∧ (0#i64).val ≤ 5253256708096
      scalar_tac
    · intro j hj hj0
      simp at hj0

theorem residual_eq : ResidualStage := by
  intro x a hx ha
  have hs := residual_spec x a hx ha
  cases heq : engine.residual x a with
  | ret r => exact ⟨r, rfl, by simpa [heq] using hs⟩
  | vis e k => simp [heq] at hs
  | div => simp [heq] at hs

theorem hidden_inner_spec (W : engine.Weights) (x : Array I64 128#usize)
    (i : Usize) (hi : i.val < 512)
    (hx : Bounded 5253256708096 x) (hw : MatrixBound 82 W.win) :
    engine.mlp_hidden_loop0_loop0 W x i 0#i64 0#usize ⦃ r =>
      r.1 = W ∧ r.2.val = TransformerInt.dot (ints x) (W.win.val.map (fun row => TransformerInt.nth 0 (row.val.map (·.val)) i.val)) ∧
      -(128 * 5253256708096 * 82) ≤ r.2.val ∧ r.2.val ≤ 128 * 5253256708096 * 82 ⦄ := by
  have hb : 0 ≤ (5253256708096 : Int) * 82 := by decide
  unfold engine.mlp_hidden_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (s : I64 × Usize) => 128 - s.2.val)
    (inv := fun (s : I64 × Usize) =>
      s.2.val ≤ 128 ∧
      s.1.val + TransformerInt.dot ((ints x).drop s.2.val)
        ((W.win.val.map (fun row => TransformerInt.nth 0 (row.val.map (·.val)) i.val)).drop s.2.val) =
          TransformerInt.dot (ints x) (W.win.val.map (fun row => TransformerInt.nth 0 (row.val.map (·.val)) i.val)) ∧
      -(s.2.val : Int) * (5253256708096 * 82) ≤ s.1.val ∧
      s.1.val ≤ (s.2.val : Int) * (5253256708096 * 82))
  · rintro ⟨acc, k⟩ ⟨hk, hacc, hlo, hhi⟩
    unfold engine.mlp_hidden_loop0_loop0.body
    dsimp only at hk hacc hlo hhi ⊢
    simp only [engine.D_MODEL]
    split
    · have hk128 : k.val < 128 := by scalar_tac
      have hkp : (k.val : Int) * (5253256708096 * 82) ≤ 128 * 5253256708096 * 82 := by
        have : (k.val : Int) ≤ 128 := by omega
        nlinarith
      have hk1p : ((k.val : Int) + 1) * (5253256708096 * 82) ≤ 128 * 5253256708096 * 82 := by
        have : (k.val : Int) + 1 ≤ 128 := by omega
        nlinarith
      rw [dot_drop _ _ _ (by simpa [ints] using hk128)
        (by simpa [List.map_map] using hk128)] at hacc
      step as ⟨xv, hxv⟩
      step as ⟨row, hrow⟩
      step as ⟨wv, hwv⟩
      have hxs := hx xv (by simp [hxv])
      have hws := hw row (by simp [hrow]) wv (by simp [hwv])
      have hp := project_mul_bound xv.val wv.val 5253256708096 82 (by decide) (by decide) hxs hws
      step as ⟨wv64, hwv64⟩
      step as ⟨p, hpv⟩
      step as ⟨acc1, hacc1⟩
      step as ⟨k1, hk1⟩
      have hxi : (ints x)[k.val]'(by simpa [ints] using hk128) = xv.val := by
        simp [ints, hxv]
      have hwi : (W.win.val.map (fun row => TransformerInt.nth 0 (row.val.map (·.val)) i.val))[k.val]'(by simpa [List.map_map] using hk128) = wv.val := by
        simp [hrow, project_nth_eq, hi, hwv]
      rw [hxi, hwi] at hacc
      simp only [hk1]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · scalar_tac
      · have hp' : p.val = xv.val * wv.val := by scalar_tac
        simp only [Nat.cast_add, Nat.cast_one, hacc1, hp']
        nlinarith only [hp.1, hlo]
      · have hp' : p.val = xv.val * wv.val := by scalar_tac
        simp only [Nat.cast_add, Nat.cast_one, hacc1, hp']
        nlinarith only [hp.2, hhi]
      · scalar_tac
    · have hk128 : k.val = 128 := by scalar_tac
      simpa [hk128, ints, TransformerInt.dot, mul_assoc] using
        And.intro (Eq.refl W) (And.intro hacc (And.intro hlo hhi))
  · simp


theorem output_inner_spec (W : engine.Weights) (x : Array I64 512#usize)
    (i : Usize) (hi : i.val < 128)
    (hx : Bounded 215384598773760 x) (hw : MatrixBound 74 W.wout) :
    engine.mlp_output_loop0_loop0 W x i 0#i64 0#usize ⦃ r =>
      r.1 = W ∧ r.2.val = TransformerInt.dot (ints x) (W.wout.val.map (fun row => TransformerInt.nth 0 (row.val.map (·.val)) i.val)) ∧
      -(512 * 215384598773760 * 74) ≤ r.2.val ∧ r.2.val ≤ 512 * 215384598773760 * 74 ⦄ := by
  have hb : 0 ≤ (215384598773760 : Int) * 74 := by decide
  unfold engine.mlp_output_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (s : I64 × Usize) => 512 - s.2.val)
    (inv := fun (s : I64 × Usize) =>
      s.2.val ≤ 512 ∧
      s.1.val + TransformerInt.dot ((ints x).drop s.2.val)
        ((W.wout.val.map (fun row => TransformerInt.nth 0 (row.val.map (·.val)) i.val)).drop s.2.val) =
          TransformerInt.dot (ints x) (W.wout.val.map (fun row => TransformerInt.nth 0 (row.val.map (·.val)) i.val)) ∧
      -(s.2.val : Int) * (215384598773760 * 74) ≤ s.1.val ∧
      s.1.val ≤ (s.2.val : Int) * (215384598773760 * 74))
  · rintro ⟨acc, k⟩ ⟨hk, hacc, hlo, hhi⟩
    unfold engine.mlp_output_loop0_loop0.body
    dsimp only at hk hacc hlo hhi ⊢
    simp only [engine.D_MLP]
    split
    · have hk512 : k.val < 512 := by scalar_tac
      have hkp : (k.val : Int) * (215384598773760 * 74) ≤ 512 * 215384598773760 * 74 := by
        have : (k.val : Int) ≤ 512 := by omega
        nlinarith
      have hk1p : ((k.val : Int) + 1) * (215384598773760 * 74) ≤ 512 * 215384598773760 * 74 := by
        have : (k.val : Int) + 1 ≤ 512 := by omega
        nlinarith
      rw [dot_drop _ _ _ (by simpa [ints] using hk512)
        (by simpa [List.map_map] using hk512)] at hacc
      step as ⟨xv, hxv⟩
      step as ⟨row, hrow⟩
      step as ⟨wv, hwv⟩
      have hxs := hx xv (by simp [hxv])
      have hws := hw row (by simp [hrow]) wv (by simp [hwv])
      have hp := project_mul_bound xv.val wv.val 215384598773760 74 (by decide) (by decide) hxs hws
      step as ⟨wv64, hwv64⟩
      step as ⟨p, hpv⟩
      step as ⟨acc1, hacc1⟩
      step as ⟨k1, hk1⟩
      have hxi : (ints x)[k.val]'(by simpa [ints] using hk512) = xv.val := by
        simp [ints, hxv]
      have hwi : (W.wout.val.map (fun row => TransformerInt.nth 0 (row.val.map (·.val)) i.val))[k.val]'(by simpa [List.map_map] using hk512) = wv.val := by
        simp [hrow, project_nth_eq, hi, hwv]
      rw [hxi, hwi] at hacc
      simp only [hk1]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · scalar_tac
      · have hp' : p.val = xv.val * wv.val := by scalar_tac
        simp only [Nat.cast_add, Nat.cast_one, hacc1, hp']
        nlinarith only [hp.1, hlo]
      · have hp' : p.val = xv.val * wv.val := by scalar_tac
        simp only [Nat.cast_add, Nat.cast_one, hacc1, hp']
        nlinarith only [hp.2, hhi]
      · scalar_tac
    · have hk512 : k.val = 512 := by scalar_tac
      simpa [hk512, ints, TransformerInt.dot, mul_assoc] using
        And.intro (Eq.refl W) (And.intro hacc (And.intro hlo hhi))
  · simp


theorem unembed_inner_spec (W : engine.Weights) (x : Array I64 128#usize)
    (i : Usize) (hi : i.val < 113)
    (hx : Bounded 124539743797248 x) (hw : MatrixBound 37 W.u) :
    engine.unembed_loop0_loop0 W x i 0#i64 0#usize ⦃ r =>
      r.1 = W ∧ r.2.val = TransformerInt.dot (ints x) (W.u.val.map (fun row => TransformerInt.nth 0 (row.val.map (·.val)) i.val)) ∧
      -(128 * 124539743797248 * 37) ≤ r.2.val ∧ r.2.val ≤ 128 * 124539743797248 * 37 ⦄ := by
  have hb : 0 ≤ (124539743797248 : Int) * 37 := by decide
  unfold engine.unembed_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (s : I64 × Usize) => 128 - s.2.val)
    (inv := fun (s : I64 × Usize) =>
      s.2.val ≤ 128 ∧
      s.1.val + TransformerInt.dot ((ints x).drop s.2.val)
        ((W.u.val.map (fun row => TransformerInt.nth 0 (row.val.map (·.val)) i.val)).drop s.2.val) =
          TransformerInt.dot (ints x) (W.u.val.map (fun row => TransformerInt.nth 0 (row.val.map (·.val)) i.val)) ∧
      -(s.2.val : Int) * (124539743797248 * 37) ≤ s.1.val ∧
      s.1.val ≤ (s.2.val : Int) * (124539743797248 * 37))
  · rintro ⟨acc, k⟩ ⟨hk, hacc, hlo, hhi⟩
    unfold engine.unembed_loop0_loop0.body
    dsimp only at hk hacc hlo hhi ⊢
    simp only [engine.D_MODEL]
    split
    · have hk128 : k.val < 128 := by scalar_tac
      have hkp : (k.val : Int) * (124539743797248 * 37) ≤ 128 * 124539743797248 * 37 := by
        have : (k.val : Int) ≤ 128 := by omega
        nlinarith
      have hk1p : ((k.val : Int) + 1) * (124539743797248 * 37) ≤ 128 * 124539743797248 * 37 := by
        have : (k.val : Int) + 1 ≤ 128 := by omega
        nlinarith
      rw [dot_drop _ _ _ (by simpa [ints] using hk128)
        (by simpa [List.map_map] using hk128)] at hacc
      step as ⟨xv, hxv⟩
      step as ⟨row, hrow⟩
      step as ⟨wv, hwv⟩
      have hxs := hx xv (by simp [hxv])
      have hws := hw row (by simp [hrow]) wv (by simp [hwv])
      have hp := project_mul_bound xv.val wv.val 124539743797248 37 (by decide) (by decide) hxs hws
      step as ⟨wv64, hwv64⟩
      step as ⟨p, hpv⟩
      step as ⟨acc1, hacc1⟩
      step as ⟨k1, hk1⟩
      have hxi : (ints x)[k.val]'(by simpa [ints] using hk128) = xv.val := by
        simp [ints, hxv]
      have hwi : (W.u.val.map (fun row => TransformerInt.nth 0 (row.val.map (·.val)) i.val))[k.val]'(by simpa [List.map_map] using hk128) = wv.val := by
        simp [hrow, project_nth_eq, hi, hwv]
      rw [hxi, hwi] at hacc
      simp only [hk1]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · scalar_tac
      · have hp' : p.val = xv.val * wv.val := by scalar_tac
        simp only [Nat.cast_add, Nat.cast_one, hacc1, hp']
        nlinarith only [hp.1, hlo]
      · have hp' : p.val = xv.val * wv.val := by scalar_tac
        simp only [Nat.cast_add, Nat.cast_one, hacc1, hp']
        nlinarith only [hp.2, hhi]
      · scalar_tac
    · have hk128 : k.val = 128 := by scalar_tac
      simpa [hk128, ints, TransformerInt.dot, mul_assoc] using
        And.intro (Eq.refl W) (And.intro hacc (And.intro hlo hhi))
  · simp



theorem unembed_spec (W : engine.Weights) (hW : LoadBounds W)
    (x : Array I64 128#usize) (hx : Bounded Envelope.final_stream x) :
    engine.unembed W x ⦃ r => ints r = TransformerInt.unembed (toModel W) (ints x) ∧
      Bounded Envelope.logit r ⦄ := by
  let target := TransformerInt.lincomb 113 (ints x) (W.u.val.map (fun row => row.val.map (·.val)))
  have hrows : ∀ row ∈ W.u.val.map (fun row => row.val.map (·.val)), row.length = 113 := by
    simp only [List.mem_map]
    rintro row ⟨r, _, rfl⟩
    simp
  have hlen : target.length = 113 := by
    simp [target, project_lincomb_length _ _ _ hrows]
  unfold engine.unembed engine.unembed_loop0
  apply loop.spec_decr_nat
    (measure := fun (s : engine.Weights × Array I64 113#usize × Usize) => 113 - s.2.2.val)
    (inv := fun (s : engine.Weights × Array I64 113#usize × Usize) =>
      s.1 = W ∧ s.2.2.val ≤ 113 ∧ Bounded Envelope.logit s.2.1 ∧
      ∀ (j : Nat) (hj : j < 113), j < s.2.2.val →
        (ints s.2.1)[j]'(by simpa [ints] using hj) = target[j]'(by omega))
  · rintro ⟨W1, out, i⟩ ⟨hW1, hi, hout, heq⟩
    dsimp only at hW1
    subst W1
    unfold engine.unembed_loop0.body
    dsimp only at hi hout heq ⊢
    simp only [engine.P]
    split
    · have him : i.val < 113 := by scalar_tac
      step with unembed_inner_spec W x i him hx hW.u as ⟨W2, acc, hW2, hacc, hlo, hhi⟩
      subst W2
      step as ⟨out1, hout1⟩
      step as ⟨i1, hi1⟩
      have htarget : acc.val = target[i.val]'(by omega) := by
        dsimp [target]
        rw [project_lincomb_get 113 (ints x) _ hrows i.val him]
        simpa [List.map_map, Function.comp_def] using hacc
      simp only [hi1]
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [hout1]
        apply project_bounded_set _ _ _ _ hout
        change -589820226623766528 ≤ acc.val ∧
          acc.val ≤ 589820226623766528
        omega
      · intro j hj hji
        by_cases hji' : j = i.val
        · subst j
          simpa [ints, hout1] using htarget
        · have hjold : j < i.val := by omega
          simpa [ints, hout1, Ne.symm hji'] using heq j hj hjold
    · have him : i.val = 113 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, hout⟩
      change ints out = target
      apply List.ext_getElem
      · simpa [ints] using hlen.symm
      · intro j hj hj'
        exact heq j (by simpa [ints] using hj) (by simpa [ints, him] using hj)
  · simp only
    refine ⟨True.intro, by scalar_tac, ?_, ?_⟩
    · intro v hv
      have : v = 0#i64 := by simpa using hv
      subst v
      change -589820226623766528 ≤ (0#i64).val ∧
        (0#i64).val ≤ 589820226623766528
      scalar_tac
    · intro j hj hj0
      simp at hj0

theorem unembed_eq : UnembedStage := by
  intro W hW x hx
  have hs := unembed_spec W hW x hx
  cases heq : engine.unembed W x with
  | ret r => exact ⟨r, rfl, by simpa [heq] using hs⟩
  | vis e k => simp [heq] at hs
  | div => simp [heq] at hs

theorem output_spec (W : engine.Weights) (hW : LoadBounds W)
    (x : Array I64 512#usize) (hx : Bounded Envelope.hidden x) :
    engine.mlp_output W x ⦃ r => ints r = TransformerInt.mlpOutput (toModel W) (ints x) ∧
      Bounded Envelope.mlp_output r ⦄ := by
  let target := TransformerInt.addV (TransformerInt.lincomb 128 (ints x) (W.wout.val.map (fun row => row.val.map (·.val)))) (ints W.bout)
  have hrows : ∀ row ∈ W.wout.val.map (fun row => row.val.map (·.val)), row.length = 128 := by
    simp only [List.mem_map]
    rintro row ⟨r, _, rfl⟩
    simp
  have hlen : target.length = 128 := by
    simp [target, project_lincomb_length _ _ _ hrows, project_addV_length, ints]
  unfold engine.mlp_output engine.mlp_output_loop0
  apply loop.spec_decr_nat
    (measure := fun (s : engine.Weights × Array I64 128#usize × Usize) => 128 - s.2.2.val)
    (inv := fun (s : engine.Weights × Array I64 128#usize × Usize) =>
      s.1 = W ∧ s.2.2.val ≤ 128 ∧ Bounded Envelope.mlp_output s.2.1 ∧
      ∀ (j : Nat) (hj : j < 128), j < s.2.2.val →
        (ints s.2.1)[j]'(by simpa [ints] using hj) = target[j]'(by omega))
  · rintro ⟨W1, out, i⟩ ⟨hW1, hi, hout, heq⟩
    dsimp only at hW1
    subst W1
    unfold engine.mlp_output_loop0.body
    dsimp only at hi hout heq ⊢
    simp only [engine.D_MODEL]
    split
    · have him : i.val < 128 := by scalar_tac
      step with output_inner_spec W x i him hx hW.wout as ⟨W2, acc, hW2, hacc, hlo, hhi⟩
      subst W2
      step as ⟨b, hb⟩
      have hbb := hW.bout b (by simp [hb])
      change -137438953472 ≤ b.val ∧ b.val ≤ 137438953472 at hbb
      step as ⟨v, hv⟩
      step as ⟨out1, hout1⟩
      step as ⟨i1, hi1⟩
      have htarget : v.val = target[i.val]'(by omega) := by
        dsimp [target]
        rw [project_addV_get _ _ (by simp [ints, project_lincomb_length _ _ _ hrows]) i.val
          (by simp [project_lincomb_length _ _ _ hrows, him])]
        rw [project_lincomb_get 128 (ints x) _ hrows i.val him]
        simp [ints, hb, hv, hacc, List.map_map, Function.comp_def]
      simp only [hi1]
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [hout1]
        apply project_bounded_set _ _ _ _ hout
        change -8160491815779172352 ≤ v.val ∧
          v.val ≤ 8160491815779172352
        scalar_tac
      · intro j hj hji
        by_cases hji' : j = i.val
        · subst j
          simpa [ints, hout1] using htarget
        · have hjold : j < i.val := by omega
          simpa [ints, hout1, Ne.symm hji'] using heq j hj hjold
    · have him : i.val = 128 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, hout⟩
      change ints out = target
      apply List.ext_getElem
      · simpa [ints] using hlen.symm
      · intro j hj hj'
        exact heq j (by simpa [ints] using hj) (by simpa [ints, him] using hj)
  · simp only
    refine ⟨True.intro, by scalar_tac, ?_, ?_⟩
    · intro v hv
      have : v = 0#i64 := by simpa using hv
      subst v
      change -8160491815779172352 ≤ (0#i64).val ∧
        (0#i64).val ≤ 8160491815779172352
      scalar_tac
    · intro j hj hj0
      simp at hj0

theorem mlp_output_eq : MlpOutputStage := by
  intro W hW x hx
  have hs := output_spec W hW x hx
  cases heq : engine.mlp_output W x with
  | ret r => exact ⟨r, rfl, by simpa [heq] using hs⟩
  | vis e k => simp [heq] at hs
  | div => simp [heq] at hs
theorem downstream_shift16_bound (v b : Int) (hlo : -b * 65536 ≤ v)
    (hhi : v ≤ b * 65536) : -b ≤ Int.shiftRight v 16 ∧ Int.shiftRight v 16 ≤ b := by
  simp only [← Int.shiftRight_eq, Int.shiftRight_eq_div_pow]
  norm_num
  omega

theorem downstream_final_length (xs ys : List Int) (h : xs.length = ys.length) :
    (TransformerInt.finalStream xs ys).length = xs.length := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys => simpa [TransformerInt.finalStream] using ih ys (by simpa using h)

theorem downstream_final_get (xs ys : List Int) (h : xs.length = ys.length)
    (i : Nat) (hi : i < xs.length) :
    (TransformerInt.finalStream xs ys)[i]'(by rw [downstream_final_length xs ys h]; exact hi) =
      Int.shiftRight (xs[i] * 256 + ys[i]'(by omega)) 16 := by
  induction xs generalizing ys i with
  | nil => simp at hi
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i => exact ih ys (by simpa using h) i (by simpa using hi)

theorem final_spec (x a : Array I64 128#usize)
    (hx : Bounded Envelope.residual x) (ha : Bounded Envelope.mlp_output a) :
    engine.final_stream x a ⦃ r => ints r = TransformerInt.finalStream (ints x) (ints a) ∧
      Bounded Envelope.final_stream r ⦄ := by
  unfold engine.final_stream engine.final_stream_loop
  apply loop.spec_decr_nat
    (measure := fun (s : Array I64 128#usize × Usize) => 128 - s.2.val)
    (inv := fun (s : Array I64 128#usize × Usize) =>
      s.2.val ≤ 128 ∧ Bounded Envelope.final_stream s.1 ∧
      ∀ (j : Nat) (hj : j < 128), j < s.2.val →
        (ints s.1)[j]'(by simpa [ints] using hj) =
          Int.shiftRight ((ints x)[j]'(by simpa [ints] using hj) * 256 +
            (ints a)[j]'(by simpa [ints] using hj)) 16)
  · rintro ⟨out, k⟩ ⟨hk, hout, heq⟩
    unfold engine.final_stream_loop.body
    dsimp only at hk hout heq ⊢
    simp only [engine.D_MODEL]
    split
    · have hk128 : k.val < 128 := by scalar_tac
      step as ⟨xv, hxv⟩
      have hxb := hx xv (by simp [hxv])
      change -5253256708096 ≤ xv.val ∧ xv.val ≤ 5253256708096 at hxb
      step as ⟨p, hp⟩
      step as ⟨av, hav⟩
      have hab := ha av (by simp [hav])
      change -8160491815779172352 ≤ av.val ∧ av.val ≤ 8160491815779172352 at hab
      step as ⟨v, hv⟩
      step as ⟨z, hz⟩
      have hzshift : z.val = Int.shiftRight (xv.val * 256 + av.val) 16 := by
        simpa [hv, hp, Int.shiftRight_eq] using hz
      have hzb : -124539743797248 ≤ z.val ∧ z.val ≤ 124539743797248 := by
        rw [hzshift]
        apply downstream_shift16_bound <;> omega
      step as ⟨out1, hout1⟩
      step as ⟨k1, hk1⟩
      simp only [hk1]
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [hout1]
        exact project_bounded_set _ _ _ _ hout hzb
      · intro j hj hjk
        by_cases hjk' : j = k.val
        · subst j
          simpa [ints, hout1, hxv, hav] using hzshift
        · have hjold : j < k.val := by omega
          simpa [ints, hout1, Ne.symm hjk'] using heq j hj hjold
    · have hk128 : k.val = 128 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, hout⟩
      apply List.ext_getElem
      · simp [ints, downstream_final_length]
      · intro j hj hj'
        rw [downstream_final_get (ints x) (ints a) (by simp [ints]) j (by simpa [ints] using hj)]
        exact heq j (by simpa [ints] using hj) (by simpa [ints, hk128] using hj)
  · simp only
    refine ⟨by scalar_tac, ?_, ?_⟩
    · intro v hv
      have : v = 0#i64 := by simpa using hv
      subst v
      change -124539743797248 ≤ (0#i64).val ∧ (0#i64).val ≤ 124539743797248
      scalar_tac
    · intro j hj hj0
      simp at hj0

theorem final_eq : FinalStage := by
  intro x a hx ha
  have hs := final_spec x a hx ha
  cases heq : engine.final_stream x a with
  | ret r => exact ⟨r, rfl, by simpa [heq] using hs⟩
  | vis e k => simp [heq] at hs
  | div => simp [heq] at hs

theorem downstream_hidden_length (xs ys : List Int) (h : xs.length = ys.length) :
    (TransformerInt.hidden xs ys).length = xs.length := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys => simpa [TransformerInt.hidden] using ih ys (by simpa using h)

theorem downstream_hidden_get (xs ys : List Int) (h : xs.length = ys.length)
    (i : Nat) (hi : i < xs.length) :
    (TransformerInt.hidden xs ys)[i]'(by rw [downstream_hidden_length xs ys h]; exact hi) =
      (let pre := xs[i] + ys[i]'(by omega) * 256
       if pre > 0 then Int.shiftRight pre 8 else 0) := by
  induction xs generalizing ys i with
  | nil => simp at hi
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i => exact ih ys (by simpa using h) i (by simpa using hi)

theorem downstream_nonneg_set {n : Usize} (x : Array I64 n) (i : Usize) (v : I64)
    (hx : ∀ z ∈ x.val, 0 ≤ z.val) (hv : 0 ≤ v.val) :
    ∀ z ∈ (x.set i v).val, 0 ≤ z.val := by
  intro z hz
  have hmem : z ∈ x.val.set i.val v := by simpa [Array.set_val_eq] using hz
  rcases List.mem_or_eq_of_mem_set hmem with hz | rfl
  · exact hx z hz
  · exact hv

set_option maxRecDepth 2048 in
theorem hidden_spec (W : engine.Weights) (hW : LoadBounds W)
    (x : Array I64 128#usize) (hx : Bounded Envelope.residual x) :
    engine.mlp_hidden W x ⦃ r => ints r = TransformerInt.mlpHidden (toModel W) (ints x) ∧
      Bounded Envelope.hidden r ∧ ∀ v ∈ r.val, 0 ≤ v.val ⦄ := by
  let lc := TransformerInt.lincomb 512 (ints x) (W.win.val.map (fun row => row.val.map (·.val)))
  let target := TransformerInt.hidden lc (ints W.bin)
  have hrows : ∀ row ∈ W.win.val.map (fun row => row.val.map (·.val)), row.length = 512 := by
    simp only [List.mem_map]
    rintro row ⟨r, _, rfl⟩
    simp
  have hlc : lc.length = 512 := project_lincomb_length _ _ _ hrows
  have hlen : target.length = 512 := by
    simpa [target, ints, hlc] using downstream_hidden_length lc (ints W.bin) (by simp [hlc, ints])
  unfold engine.mlp_hidden engine.mlp_hidden_loop0
  apply loop.spec_decr_nat
    (measure := fun (s : engine.Weights × Array I64 512#usize × Usize) => 512 - s.2.2.val)
    (inv := fun (s : engine.Weights × Array I64 512#usize × Usize) =>
      s.1 = W ∧ s.2.2.val ≤ 512 ∧ Bounded Envelope.hidden s.2.1 ∧
      (∀ v ∈ s.2.1.val, 0 ≤ v.val) ∧
      ∀ (j : Nat) (hj : j < 512),
        (ints s.2.1)[j]'(by simpa [ints] using hj) =
          if j < s.2.2.val then target[j]'(by omega) else 0)
  · rintro ⟨W1, out, i⟩ ⟨hW1, hi, hout, hnonneg, heq⟩
    dsimp only at hW1
    subst W1
    unfold engine.mlp_hidden_loop0.body
    dsimp only at hi hout hnonneg heq ⊢
    simp only [engine.D_MLP]
    split
    · have him : i.val < 512 := by scalar_tac
      step with hidden_inner_spec W x i him hx hW.win as ⟨W2, acc, hW2, hacc, hlo, hhi⟩
      subst W2
      step as ⟨b, hb⟩
      have hbb := hW.bin b (by simp [hb])
      change -1073741824 ≤ b.val ∧ b.val ≤ 1073741824 at hbb
      step as ⟨bp, hbp⟩
      step as ⟨pre, hpre⟩
      have hpreb : -55138457286082560 ≤ pre.val ∧ pre.val ≤ 55138457286082560 := by scalar_tac
      have htarget : target[i.val]'(by omega) =
          if pre.val > 0 then Int.shiftRight pre.val 8 else 0 := by
        dsimp [target]
        rw [downstream_hidden_get lc (ints W.bin) (by simp [hlc, ints]) i.val (by omega)]
        have hacc' : acc.val = lc[i.val]'(by omega) := by
          dsimp [lc]
          rw [project_lincomb_get 512 (ints x) _ hrows i.val him]
          simpa [List.map_map, Function.comp_def] using hacc
        simp only [← hacc', ints, List.getElem_map, ← hb]
        rw [hpre, hbp]
      split
      · have hpos : 0 < pre.val := by scalar_tac
        step as ⟨v, hv⟩
        have hvshift : v.val = Int.shiftRight pre.val 8 := by simpa [Int.shiftRight_eq] using hv
        have hvb : 0 ≤ v.val ∧ v.val ≤ 215384598773760 := by
          rw [hvshift]
          simp only [← Int.shiftRight_eq, Int.shiftRight_eq_div_pow]
          norm_num
          omega
        step as ⟨out1, hout1⟩
        step as ⟨i1, hi1⟩
        simp only [hi1]
        refine ⟨by omega, ?_, ?_, ?_, by omega⟩
        · rw [hout1]
          exact project_bounded_set _ _ _ _ hout (by change -215384598773760 ≤ v.val ∧ v.val ≤ 215384598773760; omega)
        · rw [hout1]
          exact downstream_nonneg_set out i v hnonneg hvb.1
        · intro j hj
          by_cases hji : j = i.val
          · subst j
            simp [ints, hout1, htarget, hpos, hvshift]
          · have hh : j < i.val + 1 ↔ j < i.val := by omega
            simpa [ints, hout1, Ne.symm hji, hh] using heq j hj
      · have hpos : ¬ 0 < pre.val := by scalar_tac
        step as ⟨i1, hi1⟩
        simp only [hi1]
        refine ⟨by omega, hout, hnonneg, ?_, by omega⟩
        intro j hj
        by_cases hji : j = i.val
        · subst j
          simpa [htarget, hpos] using heq i.val him
        · have hh : j < i.val + 1 ↔ j < i.val := by omega
          simpa [hh] using heq j hj
    · have him : i.val = 512 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, hout, hnonneg⟩
      change ints out = target
      apply List.ext_getElem
      · simpa [ints] using hlen.symm
      · intro j hj hj'
        simpa [him, show j < 512 by simpa [ints] using hj] using heq j (by simpa [ints] using hj)
  · simp only
    refine ⟨True.intro, by scalar_tac, ?_, ?_, ?_⟩
    · intro v hv
      have : v = 0#i64 := by simpa using hv
      subst v
      change -215384598773760 ≤ (0#i64).val ∧ (0#i64).val ≤ 215384598773760
      scalar_tac
    · intro v hv
      have : v = 0#i64 := by simpa using hv
      subst v
      scalar_tac
    · intro j hj
      simp only [ints, Array.repeat_val, List.getElem_map, List.getElem_replicate]
      scalar_tac
theorem mlp_hidden_eq : HiddenStage := by
  intro W hW x hx
  have hs := hidden_spec W hW x hx
  cases heq : engine.mlp_hidden W x with
  | ret r => exact ⟨r, rfl, by simpa [heq] using hs⟩
  | vis e k => simp [heq] at hs
  | div => simp [heq] at hs

#print axioms downstream_residual_length
#print axioms downstream_residual_get
#print axioms residual_spec
#print axioms residual_eq
#print axioms hidden_inner_spec
#print axioms output_inner_spec
#print axioms unembed_inner_spec
#print axioms unembed_spec
#print axioms unembed_eq
#print axioms output_spec
#print axioms mlp_output_eq
#print axioms downstream_shift16_bound
#print axioms downstream_final_length
#print axioms downstream_final_get
#print axioms final_spec
#print axioms final_eq
#print axioms downstream_hidden_length
#print axioms downstream_hidden_get
#print axioms downstream_nonneg_set
#print axioms hidden_spec
#print axioms mlp_hidden_eq
end LcnExec.Engine
