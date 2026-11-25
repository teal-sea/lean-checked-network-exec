import LcnExec.Engine.Exponential

open Aeneas Aeneas.Std Result ControlFlow
namespace LcnExec.Engine

def soft_max (s : Array I64 3#usize) : Int :=
  max (max (s.val[0]).val (s.val[1]).val) (s.val[2]).val

theorem soft_max_loop_spec (s : Array I64 3#usize) :
    engine.softmax_weights_loop0 s s.val[0] 1#usize ⦃ r => r.val = soft_max s ⦄ := by
  unfold engine.softmax_weights_loop0
  rw [loop]
  unfold engine.softmax_weights_loop0.body
  simp only [engine.N_POS]
  simp only [show (1#usize < 3#usize) = True by decide, ite_true]
  step as ⟨s1, hs1⟩
  split
  · step as ⟨j, hj⟩
    have hj' : j = 2#usize := by scalar_tac
    subst j
    rw [loop]
    dsimp only
    simp only [show (2#usize < 3#usize) = True by decide, ite_true]
    step as ⟨s2, hs2⟩
    split
    · step as ⟨j, hj⟩
      have hj' : j = 3#usize := by scalar_tac
      subst j
      rw [loop]
      dsimp only
      simp only [lt_self_iff_false, ite_false, bind_ok]
      simp only [WP.spec_ok]
      simp only [soft_max, ←hs1, ←hs2]
      scalar_tac
    · step as ⟨j, hj⟩
      have hj' : j = 3#usize := by scalar_tac
      subst j
      rw [loop]
      dsimp only
      simp only [lt_self_iff_false, ite_false, bind_ok]
      simp only [WP.spec_ok]
      simp only [soft_max, ←hs1, ←hs2]
      scalar_tac
  · step as ⟨j, hj⟩
    have hj' : j = 2#usize := by scalar_tac
    subst j
    rw [loop]
    dsimp only
    simp only [show (2#usize < 3#usize) = True by decide, ite_true]
    step as ⟨s2, hs2⟩
    split
    · step as ⟨j, hj⟩
      have hj' : j = 3#usize := by scalar_tac
      subst j
      rw [loop]
      dsimp only
      simp only [lt_self_iff_false, ite_false, bind_ok]
      simp only [WP.spec_ok]
      simp only [soft_max, ←hs1, ←hs2]
      scalar_tac
    · step as ⟨j, hj⟩
      have hj' : j = 3#usize := by scalar_tac
      subst j
      rw [loop]
      dsimp only
      simp only [lt_self_iff_false, ite_false, bind_ok]
      simp only [WP.spec_ok]
      simp only [soft_max, ←hs1, ←hs2]
      scalar_tac

#print axioms soft_max_loop_spec
def soft_exp (W : engine.Weights) (s : Array I64 3#usize) (i : Fin 3) : Int :=
  TransformerInt.expFix (toModel W) (soft_max s - (s.val[i.val]'(by simp)).val)

theorem soft_max_ge (s : Array I64 3#usize) (i : Nat) (hi : i < 3) :
    (s.val[i]'(by simpa using hi)).val ≤ soft_max s := by
  have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases h with rfl | rfl | rfl <;> simp only [soft_max] <;> omega

theorem soft_ints_three (s : Array I64 3#usize) :
    ints s = [(s.val[0]).val, (s.val[1]).val, (s.val[2]).val] := by
  apply List.ext_getElem
  · simp [ints]
  · intro i hi hi'
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by simp only [List.length_cons, List.length_nil] at hi'; omega
    rcases h with rfl | rfl | rfl <;> simp [ints]

theorem soft_exp_loop_spec (W : engine.Weights) (hW : LoadBounds W)
    (s : Array I64 3#usize) (hs : Bounded Envelope.score s)
    (m : I64) (hm : m.val = soft_max s) :
    engine.softmax_weights_loop1 W s m 0#usize (Array.repeat 3#usize 0#i64) 0#i64 ⦃ p =>
      ints p.1 = [soft_exp W s 0, soft_exp W s 1, soft_exp W s 2] ∧
      p.2.val = soft_exp W s 0 + soft_exp W s 1 + soft_exp W s 2 ∧
      (∀ v ∈ ints p.1, 0 ≤ v ∧ v ≤ 1073741824) ⦄ := by
  have hmB : -930186526720 ≤ m.val ∧ m.val ≤ 930186526720 := by
    have h0 := hs s.val[0] (List.getElem_mem _)
    have h1 := hs s.val[1] (List.getElem_mem _)
    have h2 := hs s.val[2] (List.getElem_mem _)
    simp only [Envelope.score] at h0 h1 h2
    simp only [hm, soft_max]
    omega
  unfold engine.softmax_weights_loop1
  rw [loop]
  unfold engine.softmax_weights_loop1.body
  dsimp only
  simp only [engine.N_POS, show (0#usize < 3#usize) = True by decide, ite_true]
  step as ⟨s0, hs0⟩
  have hs0B := hs s0 (by simp [hs0])
  change -930186526720 ≤ s0.val ∧ s0.val ≤ 930186526720 at hs0B
  have hs0m : s0.val ≤ m.val := by simpa only [hs0, hm] using soft_max_ge s 0 (by decide)
  step as ⟨d0, hd0⟩
  step with exp_spec W hW d0 (by scalar_tac) as ⟨v0, hv0, hv0lo, hv0hi⟩
  have hv0' : v0.val = soft_exp W s 0 := by simpa [soft_exp, hd0, hm, hs0] using hv0
  step as ⟨e0, he0⟩
  step as ⟨v0', hv0r⟩
  have hv0r' : v0'.val = v0.val := by simp [hv0r, he0]
  step as ⟨den0, hden0⟩
  step as ⟨j0, hj0⟩
  have hj0' : j0 = 1#usize := by scalar_tac
  subst j0
  rw [loop]
  dsimp only
  simp only [show (1#usize < 3#usize) = True by decide, ite_true]
  step as ⟨s1, hs1⟩
  have hs1B := hs s1 (by simp [hs1])
  change -930186526720 ≤ s1.val ∧ s1.val ≤ 930186526720 at hs1B
  have hs1m : s1.val ≤ m.val := by simpa only [hs1, hm] using soft_max_ge s 1 (by decide)
  step as ⟨d1, hd1⟩
  step with exp_spec W hW d1 (by scalar_tac) as ⟨v1, hv1, hv1lo, hv1hi⟩
  have hv1' : v1.val = soft_exp W s 1 := by simpa [soft_exp, hd1, hm, hs1] using hv1
  step as ⟨e1, he1⟩
  step as ⟨v1', hv1r⟩
  have hv1r' : v1'.val = v1.val := by simp [hv1r, he1]
  step as ⟨den1, hden1⟩
  step as ⟨j1, hj1⟩
  have hj1' : j1 = 2#usize := by scalar_tac
  subst j1
  rw [loop]
  dsimp only
  simp only [show (2#usize < 3#usize) = True by decide, ite_true]
  step as ⟨s2, hs2⟩
  have hs2B := hs s2 (by simp [hs2])
  change -930186526720 ≤ s2.val ∧ s2.val ≤ 930186526720 at hs2B
  have hs2m : s2.val ≤ m.val := by simpa only [hs2, hm] using soft_max_ge s 2 (by decide)
  step as ⟨d2, hd2⟩
  step with exp_spec W hW d2 (by scalar_tac) as ⟨v2, hv2, hv2lo, hv2hi⟩
  have hv2' : v2.val = soft_exp W s 2 := by simpa [soft_exp, hd2, hm, hs2] using hv2
  step as ⟨e2, he2⟩
  step as ⟨v2', hv2r⟩
  have hv2r' : v2'.val = v2.val := by simp [hv2r, he2]
  step as ⟨den2, hden2⟩
  step as ⟨j2, hj2⟩
  have hj2' : j2 = 3#usize := by scalar_tac
  subst j2
  rw [loop]
  dsimp only
  simp only [lt_self_iff_false, ite_false, bind_ok, WP.spec_ok]
  have heout : ints e2 = [v0.val, v1.val, v2.val] := by
    rw [soft_ints_three]
    simp [he2, he1, he0]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hv0', hv1', hv2'] using heout
  · scalar_tac
  · rw [heout]
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨hv0lo, hv0hi⟩
    · exact ⟨hv1lo, hv1hi⟩
    · exact ⟨hv2lo, hv2hi⟩

#print axioms soft_max_ge
#print axioms soft_ints_three
#print axioms soft_exp_loop_spec

theorem soft_exp_zero (W : engine.Weights) :
    TransformerInt.expFix (toModel W) 0 = 1073741824 := by
  simp [TransformerInt.expFix, TransformerInt.EXP_ONE]

theorem soft_den_bound (W : engine.Weights) (s : Array I64 3#usize)
    (hb : ∀ v ∈ [soft_exp W s 0, soft_exp W s 1, soft_exp W s 2],
      0 ≤ v ∧ v ≤ 1073741824) :
    1073741824 ≤ soft_exp W s 0 + soft_exp W s 1 + soft_exp W s 2 ∧
    soft_exp W s 0 + soft_exp W s 1 + soft_exp W s 2 ≤ 3221225472 := by
  have h0 := hb (soft_exp W s 0) (by simp)
  have h1 := hb (soft_exp W s 1) (by simp)
  have h2 := hb (soft_exp W s 2) (by simp)
  have hm : soft_max s = (s.val[0]).val ∨ soft_max s = (s.val[1]).val ∨
      soft_max s = (s.val[2]).val := by
    simp only [soft_max, max_def]
    split <;> split <;> simp
  have hone : soft_exp W s 0 = 1073741824 ∨ soft_exp W s 1 = 1073741824 ∨
      soft_exp W s 2 = 1073741824 := by
    rcases hm with hm | hm | hm
    · left; simp [soft_exp, hm, soft_exp_zero]
    · right; left; simp [soft_exp, hm, soft_exp_zero]
    · right; right; simp [soft_exp, hm, soft_exp_zero]
  omega

/-- Three rounded quotients share one denominator. Separate coordinate bounds are insufficient. -/
theorem soft_joint_bound (x y z d : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hd : 0 < d) (hs : d = x + y + z) :
    0 ≤ (x * 16777216).tdiv d ∧ 0 ≤ (y * 16777216).tdiv d ∧
    0 ≤ (z * 16777216).tdiv d ∧
    (x * 16777216).tdiv d + (y * 16777216).tdiv d +
      (z * 16777216).tdiv d ≤ 16777216 := by
  have hxp : 0 ≤ x * 16777216 := by omega
  have hyp : 0 ≤ y * 16777216 := by omega
  have hzp : 0 ≤ z * 16777216 := by omega
  refine ⟨Int.tdiv_nonneg hxp (by omega), Int.tdiv_nonneg hyp (by omega),
    Int.tdiv_nonneg hzp (by omega), ?_⟩
  rw [Int.tdiv_eq_ediv_of_nonneg hxp, Int.tdiv_eq_ediv_of_nonneg hyp,
    Int.tdiv_eq_ediv_of_nonneg hzp]
  have hxd := Int.ediv_mul_le (x * 16777216) (by omega : d ≠ 0)
  have hyd := Int.ediv_mul_le (y * 16777216) (by omega : d ≠ 0)
  have hzd := Int.ediv_mul_le (z * 16777216) (by omega : d ≠ 0)
  nlinarith

theorem soft_div_loop_spec (e : Array I64 3#usize) (den : I64)
    (he : ∀ v ∈ ints e, 0 ≤ v ∧ v ≤ 1073741824)
    (hd : 1073741824 ≤ den.val ∧ den.val ≤ 3221225472)
    (hsum : den.val = (ints e).sum) :
    engine.softmax_weights_loop2 0#usize e den (Array.repeat 3#usize 0#i64) ⦃ r =>
      ints r = [((e.val[0]).val * 16777216).tdiv den.val,
        ((e.val[1]).val * 16777216).tdiv den.val,
        ((e.val[2]).val * 16777216).tdiv den.val] ∧ AlphaBound r ⦄ := by
  have halpha : engine.ALPHA_ONE = ok 16777216#i64 := by unfold engine.ALPHA_ONE; rfl
  unfold engine.softmax_weights_loop2
  rw [loop]
  unfold engine.softmax_weights_loop2.body
  dsimp only
  simp only [engine.N_POS, show (0#usize < 3#usize) = True by decide, ite_true, halpha, bind_ok]
  step as ⟨e0, he0⟩
  have he0b := he e0.val (List.mem_map.mpr ⟨e0, by simp [he0], rfl⟩)
  step as ⟨p0, hp0⟩
  step as ⟨q0, hq0⟩
  step as ⟨a0, ha0⟩
  step as ⟨j0, hj0⟩
  have hj0' : j0 = 1#usize := by scalar_tac
  subst j0
  rw [loop]
  dsimp only
  simp only [show (1#usize < 3#usize) = True by decide, ite_true]
  step as ⟨e1, he1⟩
  have he1b := he e1.val (List.mem_map.mpr ⟨e1, by simp [he1], rfl⟩)
  step as ⟨p1, hp1⟩
  step as ⟨q1, hq1⟩
  step as ⟨a1, ha1⟩
  step as ⟨j1, hj1⟩
  have hj1' : j1 = 2#usize := by scalar_tac
  subst j1
  rw [loop]
  dsimp only
  simp only [show (2#usize < 3#usize) = True by decide, ite_true]
  step as ⟨e2, he2⟩
  have he2b := he e2.val (List.mem_map.mpr ⟨e2, by simp [he2], rfl⟩)
  step as ⟨p2, hp2⟩
  step as ⟨q2, hq2⟩
  step as ⟨a2, ha2⟩
  step as ⟨j2, hj2⟩
  have hj2' : j2 = 3#usize := by scalar_tac
  subst j2
  rw [loop]
  dsimp only
  simp only [lt_self_iff_false, ite_false, bind_ok, WP.spec_ok]
  have hout : ints a2 = [q0.val, q1.val, q2.val] := by
    rw [soft_ints_three]
    simp [ha2, ha1, ha0]
  have hsum' : den.val = e0.val + e1.val + e2.val := by
    simpa [soft_ints_three, ←he0, ←he1, ←he2, add_assoc] using hsum
  have hjoint := soft_joint_bound e0.val e1.val e2.val den.val he0b.1 he1b.1 he2b.1
    (by omega) hsum'
  have hq0' : q0.val = (e0.val * 16777216).tdiv den.val := by scalar_tac
  have hq1' : q1.val = (e1.val * 16777216).tdiv den.val := by scalar_tac
  have hq2' : q2.val = (e2.val * 16777216).tdiv den.val := by scalar_tac
  refine ⟨?_, ?_⟩
  · simp only [hout, hq0', hq1', hq2', he0, he1, he2]
  · constructor
    · intro v hv
      have hv' : v.val ∈ ints a2 := List.mem_map.mpr ⟨v, hv, rfl⟩
      rw [hout] at hv'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
      rcases hv' with hv' | hv' | hv' <;> rw [hv'] <;> omega
    · simp only [hout, List.sum_cons, List.sum_nil]
      omega

#print axioms soft_exp_zero
#print axioms soft_den_bound
#print axioms soft_joint_bound
#print axioms soft_div_loop_spec

theorem soft_max_if (a b : Int) : (if b > a then b else a) = max a b := by
  split <;> omega

theorem soft_model_eq (W : engine.Weights) (s : Array I64 3#usize) :
    (((soft_exp W s 0 * 16777216).tdiv (soft_exp W s 0 + soft_exp W s 1 + soft_exp W s 2)),
      ((soft_exp W s 1 * 16777216).tdiv (soft_exp W s 0 + soft_exp W s 1 + soft_exp W s 2)),
      ((soft_exp W s 2 * 16777216).tdiv (soft_exp W s 0 + soft_exp W s 1 + soft_exp W s 2))) =
      TransformerInt.softmaxWeights (toModel W) (triple s) := by
  simp only [triple, soft_ints_three, TransformerInt.nth, TransformerInt.softmaxWeights, soft_max_if]
  rfl

/-- Total correctness of all three actual Rust softmax loops. -/
theorem softmax_spec (W : engine.Weights) (hW : LoadBounds W)
    (s : Array I64 3#usize) (hs : Bounded Envelope.score s) :
    engine.softmax_weights W s ⦃ r =>
      triple r = TransformerInt.softmaxWeights (toModel W) (triple s) ∧ AlphaBound r ⦄ := by
  unfold engine.softmax_weights
  step as ⟨s0, hs0⟩
  subst s0
  step with soft_max_loop_spec s as ⟨m, hm⟩
  step with soft_exp_loop_spec W hW s hs m hm as ⟨e, den, he, hden, heb⟩
  have hb : ∀ v ∈ [soft_exp W s 0, soft_exp W s 1, soft_exp W s 2],
      0 ≤ v ∧ v ≤ 1073741824 := by rw [←he]; exact heb
  have hd : 1073741824 ≤ den.val ∧ den.val ≤ 3221225472 := by
    rw [hden]
    exact soft_den_bound W s hb
  have hsum : den.val = (ints e).sum := by simp [he, hden, add_assoc]
  step with soft_div_loop_spec e den heb hd hsum as ⟨r, hr, hrb⟩
  refine ⟨?_, hrb⟩
  have he0 : (e.val[0]).val = soft_exp W s 0 := by
    have h := congrArg (fun xs => TransformerInt.nth 0 xs 0) he
    simpa only [soft_ints_three, TransformerInt.nth] using h
  have he1 : (e.val[1]).val = soft_exp W s 1 := by
    have h := congrArg (fun xs => TransformerInt.nth 0 xs 1) he
    simpa only [soft_ints_three, TransformerInt.nth] using h
  have he2 : (e.val[2]).val = soft_exp W s 2 := by
    have h := congrArg (fun xs => TransformerInt.nth 0 xs 2) he
    simpa only [soft_ints_three, TransformerInt.nth] using h
  simp only [triple, hr, TransformerInt.nth, he0, he1, he2, hden]
  exact soft_model_eq W s

/-- The exact frozen softmax stage, including nonnegativity and the joint sum bound. -/
theorem softmax_eq : SoftmaxStage := by
  intro W hW s hs
  have h := softmax_spec W hW s hs
  cases heq : engine.softmax_weights W s with
  | ret r => exact ⟨r, rfl, by simpa [heq] using h⟩
  | vis i k => simp [heq] at h
  | div => simp [heq] at h

#print axioms soft_max_if
#print axioms soft_model_eq
#print axioms softmax_spec
#print axioms softmax_eq

end LcnExec.Engine
