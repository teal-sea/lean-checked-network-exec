import LcnExec.Engine.Downstream

open Aeneas Aeneas.Std Result ControlFlow
namespace LcnExec.Engine

theorem mixing_length (a b c : Int) (xs ys zs : List Int)
    (hy : xs.length = ys.length) (hz : xs.length = zs.length) :
    (TransformerInt.mix a b c xs ys zs).length = xs.length := by
  induction xs generalizing ys zs with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hy
    | cons y ys =>
      cases zs with
      | nil => simp at hz
      | cons z zs => simpa [TransformerInt.mix] using ih ys zs (by simpa using hy) (by simpa using hz)

theorem mixing_get (a b c : Int) (xs ys zs : List Int)
    (hy : xs.length = ys.length) (hz : xs.length = zs.length) (i : Nat) (hi : i < xs.length) :
    (TransformerInt.mix a b c xs ys zs)[i]'(by rw [mixing_length a b c xs ys zs hy hz]; exact hi) =
      Int.shiftRight (a * xs[i] + b * ys[i]'(by omega) + c * zs[i]'(by omega)) 16 := by
  induction xs generalizing ys zs i with
  | nil => simp at hi
  | cons x xs ih =>
    cases ys with
    | nil => simp at hy
    | cons y ys =>
      cases zs with
      | nil => simp at hz
      | cons z zs =>
        cases i with
        | zero => rfl
        | succ i => exact ih ys zs (by simpa using hy) (by simpa using hz) i (by simpa using hi)

theorem mixing_alpha (a : Array I64 3#usize) (ha : AlphaBound a) :
    0 ≤ (ints a)[0]'(by simp [ints]) ∧
    0 ≤ (ints a)[1]'(by simp [ints]) ∧
    0 ≤ (ints a)[2]'(by simp [ints]) ∧
    (ints a)[0]'(by simp [ints]) + (ints a)[1]'(by simp [ints]) +
      (ints a)[2]'(by simp [ints]) ≤ 16777216 := by
  have hlen : a.val.length = 3 := by simp
  have hlist : a.val = [a.val[0]'(by omega), a.val[1]'(by omega), a.val[2]'(by omega)] := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      have : i = 0 ∨ i = 1 ∨ i = 2 := by simp at hi; omega
      rcases this with rfl | rfl | rfl <;> rfl
  rcases ha with ⟨hn, hs⟩
  have h0 := hn a.val[0] (List.getElem_mem (by omega))
  have h1 := hn a.val[1] (List.getElem_mem (by omega))
  have h2 := hn a.val[2] (List.getElem_mem (by omega))
  refine ⟨by simpa [ints] using h0, by simpa [ints] using h1, by simpa [ints] using h2, ?_⟩
  change (a.val.map (·.val)).sum ≤ 16777216 at hs
  rw [hlist] at hs
  simpa [ints, add_assoc] using hs

theorem mixing_weighted_bound (a b c x y z : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a+b+c ≤ 16777216)
    (hx : -1723136 ≤ x ∧ x ≤ 1723136)
    (hy : -1723136 ≤ y ∧ y ≤ 1723136)
    (hz : -1723136 ≤ z ∧ z ≤ 1723136) :
    -28909424869376 ≤ a*x+b*y+c*z ∧ a*x+b*y+c*z ≤ 28909424869376 := by
  constructor <;> nlinarith [mul_nonneg ha (by omega : 0 ≤ x + 1723136),
    mul_nonneg hb (by omega : 0 ≤ y + 1723136), mul_nonneg hc (by omega : 0 ≤ z + 1723136),
    mul_nonneg ha (by omega : 0 ≤ 1723136 - x), mul_nonneg hb (by omega : 0 ≤ 1723136 - y),
    mul_nonneg hc (by omega : 0 ≤ 1723136 - z)]

theorem mixing_spec (a : Array I64 3#usize) (v0 v1 v2 : Array I64 32#usize)
    (ha : AlphaBound a) (h0 : Bounded Envelope.value v0)
    (h1 : Bounded Envelope.value v1) (h2 : Bounded Envelope.value v2) :
    engine.head_output_loop0 a v0 v1 v2 (Array.repeat 32#usize 0#i64) 0#usize ⦃ r =>
      ints r = TransformerInt.mix (triple a).1 (triple a).2.1 (triple a).2.2
        (ints v0) (ints v1) (ints v2) ∧ Bounded Envelope.mixed_value r ⦄ := by
  let a0 := (ints a)[0]'(by simp [ints])
  let a1 := (ints a)[1]'(by simp [ints])
  let a2 := (ints a)[2]'(by simp [ints])
  let target := TransformerInt.mix a0 a1 a2 (ints v0) (ints v1) (ints v2)
  have hat := mixing_alpha a ha
  change 0 ≤ a0 ∧ 0 ≤ a1 ∧ 0 ≤ a2 ∧ a0+a1+a2 ≤ 16777216 at hat
  have hlen : target.length = 32 := by
    simpa [target, ints] using mixing_length a0 a1 a2 (ints v0) (ints v1) (ints v2) (by simp [ints]) (by simp [ints])
  unfold engine.head_output_loop0
  apply loop.spec_decr_nat
    (measure := fun (s : Array I64 32#usize × Usize) => 32 - s.2.val)
    (inv := fun (s : Array I64 32#usize × Usize) =>
      s.2.val ≤ 32 ∧ Bounded Envelope.mixed_value s.1 ∧
      ∀ (j : Nat) (hj : j < 32), j < s.2.val →
        (ints s.1)[j]'(by simpa [ints] using hj) = target[j]'(by omega))
  · rintro ⟨out, i⟩ ⟨hi, hout, heq⟩
    unfold engine.head_output_loop0.body
    dsimp only at hi hout heq ⊢
    simp only [engine.D_HEAD]
    split
    · have him : i.val < 32 := by scalar_tac
      step as ⟨av0, hav0⟩
      step as ⟨x0, hx0⟩
      have hx0b := h0 x0 (by simp [hx0])
      have hav0' : av0.val = a0 := by simp [a0, ints, hav0]
      have hp0b := project_mul_bound av0.val x0.val 16777216 1723136 (by decide) (by decide)
        (by omega) hx0b
      step as ⟨p0, hp0⟩
      step as ⟨av1, hav1⟩
      step as ⟨x1, hx1⟩
      have hx1b := h1 x1 (by simp [hx1])
      have hav1' : av1.val = a1 := by simp [a1, ints, hav1]
      have hp1b := project_mul_bound av1.val x1.val 16777216 1723136 (by decide) (by decide)
        (by omega) hx1b
      step as ⟨p1, hp1⟩
      step as ⟨s01, hs01⟩
      step as ⟨av2, hav2⟩
      step as ⟨x2, hx2⟩
      have hx2b := h2 x2 (by simp [hx2])
      have hav2' : av2.val = a2 := by simp [a2, ints, hav2]
      have hp2b := project_mul_bound av2.val x2.val 16777216 1723136 (by decide) (by decide)
        (by omega) hx2b
      step as ⟨p2, hp2⟩
      have hsum := mixing_weighted_bound a0 a1 a2 x0.val x1.val x2.val
        hat.1 hat.2.1 hat.2.2.1 hat.2.2.2 hx0b hx1b hx2b
      step as ⟨s, hs⟩
      step as ⟨v, hv⟩
      have hvshift : v.val = Int.shiftRight (a0*x0.val+a1*x1.val+a2*x2.val) 16 := by
        simpa [hs, hs01, hp0, hp1, hp2, hav0', hav1', hav2', Int.shiftRight_eq] using hv
      have hvb : -441122816 ≤ v.val ∧ v.val ≤ 441122816 := by
        rw [hvshift]
        apply downstream_shift16_bound <;> omega
      step as ⟨out1, hout1⟩
      step as ⟨i1, hi1⟩
      have htarget : v.val = target[i.val]'(by omega) := by
        dsimp [target]
        rw [mixing_get _ _ _ _ _ _ (by simp [ints]) (by simp [ints]) i.val (by simp [ints, him])]
        simpa [ints, hx0, hx1, hx2] using hvshift
      simp only [hi1]
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [hout1]
        exact project_bounded_set _ _ _ _ hout hvb
      · intro j hj hji
        by_cases hji' : j = i.val
        · subst j
          simpa [ints, hout1] using htarget
        · have hjold : j < i.val := by omega
          simpa [ints, hout1, Ne.symm hji'] using heq j hj hjold
    · have him : i.val = 32 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, hout⟩
      have ht : TransformerInt.mix (triple a).1 (triple a).2.1 (triple a).2.2
          (ints v0) (ints v1) (ints v2) = target := by
        simp [triple, project_nth_eq, ints, target, a0, a1, a2]
      rw [ht]
      apply List.ext_getElem
      · simpa [ints] using hlen.symm
      · intro j hj hj'
        exact heq j (by simpa [ints] using hj) (by simpa [ints, him] using hj)
  · simp only
    refine ⟨by scalar_tac, ?_, ?_⟩
    · intro v hv
      have : v = 0#i64 := by simpa using hv
      subst v
      change -441122816 ≤ (0#i64).val ∧ (0#i64).val ≤ 441122816
      scalar_tac
    · intro j hj hj0
      simp at hj0

theorem head_inner_spec (x : Array I64 32#usize)
    (w : Array (Array (Array I8 128#usize) 32#usize) 4#usize) (h i : Usize)
    (hh : h.val < 4) (hi : i.val < 128)
    (hx : Bounded Envelope.mixed_value x) (hw : TensorBound 93 w) :
    engine.head_output_loop1_loop0 w h x i 0#i64 0#usize ⦃ r =>
      r.val = TransformerInt.dot (ints x) ((w.val[h.val]'(by simpa using hh)).val.map (fun row => TransformerInt.nth 0 (row.val.map (·.val)) i.val)) ∧
      -(32 * 441122816 * 93) ≤ r.val ∧ r.val ≤ 32 * 441122816 * 93 ⦄ := by
  have hb : 0 ≤ (441122816 : Int) * 93 := by decide
  unfold engine.head_output_loop1_loop0
  apply loop.spec_decr_nat
    (measure := fun (s : I64 × Usize) => 32 - s.2.val)
    (inv := fun (s : I64 × Usize) =>
      s.2.val ≤ 32 ∧
      s.1.val + TransformerInt.dot ((ints x).drop s.2.val)
        (((w.val[h.val]'(by simpa using hh)).val.map (fun row => TransformerInt.nth 0 (row.val.map (·.val)) i.val)).drop s.2.val) =
          TransformerInt.dot (ints x) ((w.val[h.val]'(by simpa using hh)).val.map (fun row => TransformerInt.nth 0 (row.val.map (·.val)) i.val)) ∧
      -(s.2.val : Int) * (441122816 * 93) ≤ s.1.val ∧
      s.1.val ≤ (s.2.val : Int) * (441122816 * 93))
  · rintro ⟨acc, k⟩ ⟨hk, hacc, hlo, hhi⟩
    unfold engine.head_output_loop1_loop0.body
    dsimp only at hk hacc hlo hhi ⊢
    simp only [engine.D_HEAD]
    split
    · have hk32 : k.val < 32 := by scalar_tac
      have hkp : (k.val : Int) * (441122816 * 93) ≤ 32 * 441122816 * 93 := by
        have : (k.val : Int) ≤ 32 := by omega
        nlinarith
      have hk1p : ((k.val : Int) + 1) * (441122816 * 93) ≤ 32 * 441122816 * 93 := by
        have : (k.val : Int) + 1 ≤ 32 := by omega
        nlinarith
      rw [dot_drop _ _ _ (by simpa [ints] using hk32)
        (by simpa [List.map_map] using hk32)] at hacc
      step as ⟨xv, hxv⟩
      step as ⟨mat, hmat⟩
      step as ⟨row, hrow⟩
      step as ⟨wv, hwv⟩
      have hxs := hx xv (by simp [hxv])
      have hws := hw mat (by simp [hmat]) row (by simp [hrow]) wv (by simp [hwv])
      have hp := project_mul_bound xv.val wv.val 441122816 93 (by decide) (by decide) hxs hws
      step as ⟨wv64, hwv64⟩
      step as ⟨p, hpv⟩
      step as ⟨acc1, hacc1⟩
      step as ⟨k1, hk1⟩
      have hxi : (ints x)[k.val]'(by simpa [ints] using hk32) = xv.val := by
        simp [ints, hxv]
      have hwi : ((w.val[h.val]'(by simpa using hh)).val.map (fun row => TransformerInt.nth 0 (row.val.map (·.val)) i.val))[k.val]'(by simpa [List.map_map] using hk32) = wv.val := by
        simp [hmat, hrow, project_nth_eq, hi, hwv]
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
    · have hk32 : k.val = 32 := by scalar_tac
      simpa [hk32, ints, List.map_map, TransformerInt.dot, mul_assoc] using
        And.intro hacc (And.intro hlo hhi)
  · simp


theorem head_linear_spec (x : Array I64 32#usize)
    (w : Array (Array (Array I8 128#usize) 32#usize) 4#usize) (h : Usize)
    (hh : h.val < 4) (hx : Bounded Envelope.mixed_value x) (hw : TensorBound 93 w) :
    engine.head_output_loop1 w h x (Array.repeat 128#usize 0#i64) 0#usize ⦃ r =>
      ints r = TransformerInt.lincomb 128 (ints x)
        ((w.val[h.val]'(by simpa using hh)).val.map (fun row => row.val.map (·.val))) ∧
      Bounded Envelope.head_output r ⦄ := by
  let mat := w.val[h.val]'(by simpa using hh)
  let target := TransformerInt.lincomb 128 (ints x) (mat.val.map (fun row => row.val.map (·.val)))
  have hrows : ∀ row ∈ mat.val.map (fun row => row.val.map (·.val)), row.length = 128 := by
    simp only [List.mem_map]
    rintro row ⟨r, _, rfl⟩
    simp
  have hlen : target.length = 128 := project_lincomb_length _ _ _ hrows
  unfold engine.head_output_loop1
  apply loop.spec_decr_nat
    (measure := fun (s : Array I64 128#usize × Usize) => 128 - s.2.val)
    (inv := fun (s : Array I64 128#usize × Usize) =>
      s.2.val ≤ 128 ∧ Bounded Envelope.head_output s.1 ∧
      ∀ (j : Nat) (hj : j < 128), j < s.2.val →
        (ints s.1)[j]'(by simpa [ints] using hj) = target[j]'(by omega))
  · rintro ⟨out, i⟩ ⟨hi, hout, heq⟩
    unfold engine.head_output_loop1.body
    dsimp only at hi hout heq ⊢
    simp only [engine.D_MODEL]
    split
    · have him : i.val < 128 := by scalar_tac
      step with head_inner_spec x w h i hh him hx hw as ⟨acc, hacc, hlo, hhi⟩
      step as ⟨out1, hout1⟩
      step as ⟨i1, hi1⟩
      have htarget : acc.val = target[i.val]'(by omega) := by
        dsimp [target]
        rw [project_lincomb_get 128 (ints x) _ hrows i.val him]
        simpa [mat, List.map_map, Function.comp_def] using hacc
      simp only [hi1]
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [hout1]
        exact project_bounded_set _ _ _ _ hout ⟨hlo, hhi⟩
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
    refine ⟨by scalar_tac, ?_, ?_⟩
    · intro v hv
      have : v = 0#i64 := by simpa using hv
      subst v
      change -1312781500416 ≤ (0#i64).val ∧ (0#i64).val ≤ 1312781500416
      scalar_tac
    · intro j hj hj0
      simp at hj0

theorem head_output_spec (W : engine.Weights) (hW : LoadBounds W) (h : Usize)
    (x : Array (Array I64 128#usize) 3#usize) (a : Array I64 3#usize)
    (hh : h.val < 4) (hx : streams x) (ha : AlphaBound a) :
    engine.head_output W h x a ⦃ r =>
      ints r = TransformerInt.headOutput (toModel W) h.val (stream x 0) (stream x 1) (stream x 2) (triple a) ∧
      Bounded Envelope.head_output r ⦄ := by
  unfold engine.head_output
  step as ⟨x0, hx0⟩
  step as ⟨w, hw⟩
  have hx0b := hx x0 (by simp [hx0])
  have hwb := hW.wv w (by simp [hw])
  step with project_spec x0 w Envelope.embedding 106 (by decide) (by decide) hx0b hwb (by decide)
    as ⟨v0, hv0, hv0b⟩
  step as ⟨x1, hx1⟩
  have hx1b := hx x1 (by simp [hx1])
  step with project_spec x1 w Envelope.embedding 106 (by decide) (by decide) hx1b hwb (by decide)
    as ⟨v1, hv1, hv1b⟩
  step as ⟨x2, hx2⟩
  have hx2b := hx x2 (by simp [hx2])
  step with project_spec x2 w Envelope.embedding 106 (by decide) (by decide) hx2b hwb (by decide)
    as ⟨v2, hv2, hv2b⟩
  have h0 : Bounded Envelope.value v0 := by simpa [Envelope.embedding, Envelope.value] using hv0b
  have h1 : Bounded Envelope.value v1 := by simpa [Envelope.embedding, Envelope.value] using hv1b
  have h2 : Bounded Envelope.value v2 := by simpa [Envelope.embedding, Envelope.value] using hv2b
  step with mixing_spec a v0 v1 v2 ha h0 h1 h2 as ⟨z, hz, hzb⟩
  step with head_linear_spec z W.wo h hh hzb hW.wo as ⟨r, hr, hrb⟩
  refine ⟨?_, hrb⟩
  rw [hr, hz, hv0, hv1, hv2]
  have hs0 : stream x 0 = ints x0 := by simp [stream, project_nth_eq, ints, hx0]
  have hs1 : stream x 1 = ints x1 := by simp [stream, project_nth_eq, ints, hx1]
  have hs2 : stream x 2 = ints x2 := by simp [stream, project_nth_eq, ints, hx2]
  simp [TransformerInt.headOutput, TransformerInt.value, hs0, hs1, hs2,
    toModel, project_nth_eq, hh, hw]

theorem head_output_eq : HeadOutputStage := by
  intro W hW h x a hh hx ha
  have hs := head_output_spec W hW h x a hh hx ha
  cases heq : engine.head_output W h x a with
  | ret r => exact ⟨r, rfl, by simpa [heq] using hs⟩
  | vis e k => simp [heq] at hs
  | div => simp [heq] at hs

#print axioms mixing_length
#print axioms mixing_get
#print axioms mixing_alpha
#print axioms mixing_weighted_bound
#print axioms mixing_spec
#print axioms head_inner_spec
#print axioms head_linear_spec
#print axioms head_output_spec
#print axioms head_output_eq
end LcnExec.Engine
