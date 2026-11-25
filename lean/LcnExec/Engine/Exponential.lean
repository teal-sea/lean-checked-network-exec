import LcnExec.Engine.Projection

open Aeneas Aeneas.Std Result ControlFlow
namespace LcnExec.Engine

/-- The byte mask is exactly Euclidean reduction, including the signed representation. -/
theorem exp_mask (x : I64) : (x &&& 255#i64).val = x.val % 256 := by
  change (x.bv &&& (255 : BitVec 64)).toInt = x.bv.toInt % 256
  have hm : (x.bv &&& (255 : BitVec 64)).toNat = x.bv.toNat % 256 := by
    simpa [BitVec.toNat_and] using Nat.and_two_pow_sub_one_eq_mod x.bv.toNat 8
  rw [BitVec.toInt_eq_toNat_cond, hm, BitVec.toInt_eq_toNat_cond]
  norm_num
  split <;> omega

/-- Each table multiplication is nonnegative and fits the frozen product envelope. -/
theorem exp_mul_bound (x y : Int) (hx : 0 ≤ x ∧ x ≤ 1073741824)
    (hy : 0 ≤ y ∧ y ≤ 1073741824) :
    0 ≤ x * y ∧ x * y ≤ Envelope.exp_product := by
  change 0 ≤ x * y ∧ x * y ≤ 1152921504606846976
  constructor
  · exact mul_nonneg hx.1 hy.1
  · nlinarith [mul_nonneg (by omega : 0 ≤ 1073741824 - x) hy.1]

theorem exp_shift_bound (x : Int) (hx : 0 ≤ x ∧ x ≤ Envelope.exp_product) :
    0 ≤ Int.shiftRight x 30 ∧ Int.shiftRight x 30 ≤ 1073741824 := by
  change 0 ≤ x ∧ x ≤ 1152921504606846976 at hx
  change 0 ≤ x >>> 30 ∧ x >>> 30 ≤ 1073741824
  rw [Int.shiftRight_eq_div_pow]
  norm_num
  omega

theorem exp_table_nth {n : Usize} (a : Array I64 n) (i : Usize) (hi : i.val < n.val) :
    TransformerInt.nth 0 (a.val.map (·.val)) i.val = (a.val[i.val]'(by simpa using hi)).val := by
  rw [project_nth_eq _ _ _ (by simpa using hi), List.getElem_map]

theorem exp_spec (W : engine.Weights) (hW : LoadBounds W) (d : I64) (_hd : 0 ≤ d.val) :
    engine.exp_fix W d ⦃ r => r.val = TransformerInt.expFix (toModel W) d.val ∧
      0 ≤ r.val ∧ r.val ≤ 1073741824 ⦄ := by
  unfold engine.exp_fix
  simp only [engine.EXP_FRAC_BITS]
  split
  · have hz : d.val ≤ 0 := by scalar_tac
    have hone : engine.EXP_ONE = ok 1073741824#i64 := by unfold engine.EXP_ONE; rfl
    simp [hone, TransformerInt.expFix, hz, TransformerInt.EXP_ONE]
  · have hpos : ¬d.val ≤ 0 := by scalar_tac
    step as ⟨u, hu, _⟩
    step as ⟨n, hn, _⟩
    change u.val = Int.shiftRight d.val 8 at hu
    change n.val = Int.shiftRight u.val 24 at hn
    have hu0 : 0 ≤ u.val := by rw [hu]; change 0 ≤ d.val >>> 8; rw [Int.shiftRight_eq_div_pow]; omega
    have hn0 : 0 ≤ n.val := by rw [hn]; change 0 ≤ u.val >>> 24; rw [Int.shiftRight_eq_div_pow]; omega
    simp only [engine.EXP_N_LEN]
    split
    · have hn32 : 32 ≤ n.val := by scalar_tac
      simp [TransformerInt.expFix, hpos, ←hu, ←hn, hn32]
    · have hn32 : n.val < 32 := by scalar_tac
      step as ⟨i, hi, _⟩
      step as ⟨b2, hb2, _⟩
      rw [exp_mask] at hb2
      change i.val = Int.shiftRight u.val 16 at hi
      change b2.val = Int.emod i.val 256 at hb2
      rw [hi] at hb2
      step as ⟨i1, hi1, _⟩
      step as ⟨b1, hb1, _⟩
      rw [exp_mask] at hb1
      change i1.val = Int.shiftRight u.val 8 at hi1
      change b1.val = Int.emod i1.val 256 at hb1
      rw [hi1] at hb1
      step as ⟨b0, hb0, _⟩
      rw [exp_mask] at hb0
      change b0.val = Int.emod u.val 256 at hb0
      have hb2b : 0 ≤ b2.val ∧ b2.val < 256 := by
        change b2.val = (u.val >>> 16) % 256 at hb2
        omega
      have hb1b : 0 ≤ b1.val ∧ b1.val < 256 := by
        change b1.val = (u.val >>> 8) % 256 at hb1
        omega
      have hb0b : 0 ≤ b0.val ∧ b0.val < 256 := by
        change b0.val = u.val % 256 at hb0
        omega
      step with IScalar.hcast_inBounds_spec as ⟨ni, hni⟩
      step as ⟨e, he⟩
      have heb := hW.exp_n e (by simp [he])
      step with IScalar.hcast_inBounds_spec as ⟨j2, hj2⟩
      step as ⟨t2, ht2⟩
      have ht2b := hW.exp_2 t2 (by simp [ht2])
      have hp2 := exp_mul_bound e.val t2.val heb ht2b
      change 0 ≤ e.val * t2.val ∧ e.val * t2.val ≤ 1152921504606846976 at hp2
      step as ⟨p2, hp2v⟩
      step as ⟨e1, he1, _⟩
      have he1b : 0 ≤ e1.val ∧ e1.val ≤ 1073741824 := by
        rw [he1, hp2v]
        exact exp_shift_bound _ hp2
      step with IScalar.hcast_inBounds_spec as ⟨j1, hj1⟩
      step as ⟨t1, ht1⟩
      have ht1b := hW.exp_1 t1 (by simp [ht1])
      have hp1 := exp_mul_bound e1.val t1.val he1b ht1b
      change 0 ≤ e1.val * t1.val ∧ e1.val * t1.val ≤ 1152921504606846976 at hp1
      step as ⟨p1, hp1v⟩
      step as ⟨e2, he2, _⟩
      have he2b : 0 ≤ e2.val ∧ e2.val ≤ 1073741824 := by
        rw [he2, hp1v]
        exact exp_shift_bound _ hp1
      step with IScalar.hcast_inBounds_spec as ⟨j0, hj0⟩
      step as ⟨t0, ht0⟩
      have ht0b := hW.exp_0 t0 (by simp [ht0])
      have hp0 := exp_mul_bound e2.val t0.val he2b ht0b
      change 0 ≤ e2.val * t0.val ∧ e2.val * t0.val ≤ 1152921504606846976 at hp0
      step as ⟨p0, hp0v⟩
      step as ⟨r, hr, _⟩
      have hrb : 0 ≤ r.val ∧ r.val ≤ 1073741824 := by
        rw [hr, hp0v]
        exact exp_shift_bound _ hp0
      refine ⟨?_, hrb⟩
      have hni' : ni.val = n.val.toNat := by omega
      have hj2' : j2.val = b2.val.toNat := by omega
      have hj1' : j1.val = b1.val.toNat := by omega
      have hj0' : j0.val = b0.val.toNat := by omega
      simp only [TransformerInt.expFix, hpos, ite_false, ←hu, ←hn,
        show ¬32 ≤ n.val by omega, toModel]
      rw [←hb2, ←hb1, ←hb0, ←hni', ←hj2', ←hj1', ←hj0']
      rw [exp_table_nth W.exp_n ni (by scalar_tac),
        exp_table_nth W.exp_2 j2 (by scalar_tac),
        exp_table_nth W.exp_1 j1 (by scalar_tac),
        exp_table_nth W.exp_0 j0 (by scalar_tac)]
      simp only [←he, ←ht2, ←ht1, ←ht0]
      rw [hr, hp0v, he2, hp1v, he1, hp2v]
      rfl

/-- The frozen exact exponential stage, with no stronger load assumptions. -/
theorem exp_eq : ExpStage := by
  intro W hW d hd
  have h := exp_spec W hW d hd
  cases heq : engine.exp_fix W d with
  | ret r => exact ⟨r, rfl, by simpa [heq] using h⟩
  | vis i k => simp [heq] at h
  | div => simp [heq] at h

/-- Exact zero case of the translated Rust exponential, independent of the tables. -/
theorem exp_zero_eq (W : engine.Weights) :
    engine.exp_fix W 0#i64 = ok 1073741824#i64 := by
  unfold engine.exp_fix engine.EXP_ONE
  rfl

#print axioms exp_zero_eq
#print axioms exp_table_nth
#print axioms exp_spec
#print axioms exp_eq

#print axioms exp_mask
#print axioms exp_mul_bound
#print axioms exp_shift_bound
end LcnExec.Engine
