import LcnExec.Translated.Adder
import RnnAdder.Trained

/-! Gate 1A: Aeneas's translation of `rust/adder` computes what `RnnAdder` computes, for every
input, with total correctness: each function returns `ok`, so it neither fails nor diverges.

The weights reach these theorems through the translation of `rust/adder/src/weights.rs`, the
constants `adder.weights.*` of `LcnExec/Translated/Adder.lean`. `rustNet` is the network read off
those constants and `rustNet_eq` proves it equal to `RnnAdder.Trained.net`. No weight is written
in this file.

The theorems the gates check are in the last section. Before it, one `spec` per Rust function:
a total-correctness triple `f args ⦃ r => post r ⦄` (`Aeneas.Std.WP.spec`). -/

open Aeneas Aeneas.Std Result ControlFlow

namespace LcnExec.Adder

open RnnAdder (Net dotB thr unit layer run runState finalCarry bitsToNat)
open RnnAdder.Trained (net)

/-! ## From a total-correctness triple to an equation -/

/-- A total-correctness triple pins the computation down: it is `ok v` for some `v` satisfying
the postcondition (failure, divergence and effects all make the triple false). The same lemma as
`LcnExec.Smoke.eq_ok_of_spec`, repeated so that this file does not depend on the smoke test. -/
theorem eq_ok_of_spec {α : Type} {m : Result α} {p : α → Prop} (h : m ⦃ x => p x ⦄) :
    ∃ v, m = ok v ∧ p v := by
  cases m with
  | ret r => exact ⟨r, rfl, by simpa using h⟩
  | vis i k => simp at h
  | div => simp at h

/-! ## The weights -/

/-- The integer values of an array of `i32`. -/
def ints {n : Usize} (w : Array I32 n) : List Int := w.val.map (·.val)

@[simp] theorem ints_length {n : Usize} (w : Array I32 n) : (ints w).length = n.val := by
  simp [ints]

/-- The network read off the translated Rust constants. -/
def rustNet : Net where
  Wh := adder.weights.WH.val.map ints
  Wxa := ints adder.weights.WXA
  Wxb := ints adder.weights.WXB
  bh := ints adder.weights.BH
  Wo := ints adder.weights.WO
  Woa := adder.weights.WOA.val
  Wob := adder.weights.WOB.val
  bo := adder.weights.BO.val
  Wc := ints adder.weights.WC
  bc := adder.weights.BC.val
  h0 := adder.weights.H0.val
  reach := adder.weights.REACH.val.map (·.val)

/-- The translated constants of `weights.rs` are the entries of `RnnAdder.Trained.net`. -/
theorem rustNet_eq : rustNet = net := by
  simp [rustNet, ints, adder.weights.WH, adder.weights.WXA, adder.weights.WXB, adder.weights.BH,
    adder.weights.WO, adder.weights.WOA, adder.weights.WOB, adder.weights.BO, adder.weights.WC,
    adder.weights.BC, adder.weights.H0, adder.weights.REACH, net]

theorem H0_eq : adder.weights.H0.val = net.h0 := congrArg Net.h0 rustNet_eq

@[simp, scalar_tac_simps]
theorem H_val : adder.weights.H.val = 4 := by simp [adder.weights.H]

@[simp] theorem rustNet_Wh_length : rustNet.Wh.length = 4 := by simp [rustNet]
@[simp] theorem rustNet_Wxa_length : rustNet.Wxa.length = 4 := by simp [rustNet]
@[simp] theorem rustNet_Wxb_length : rustNet.Wxb.length = 4 := by simp [rustNet]
@[simp] theorem rustNet_bh_length : rustNet.bh.length = 4 := by simp [rustNet]

/-- Every entry is a whole number in [-127, 127]. With 4 units this bounds every pre-activation
by 4 * 127 + 3 * 127 = 889 in absolute value, so no `i32` addition overflows. -/
def Small {n : Usize} (w : Array I32 n) : Prop := ∀ x ∈ w.val, -127 ≤ x.val ∧ x.val ≤ 127

theorem WH_small : ∀ row ∈ adder.weights.WH.val, Small row := by
  simp [Small, adder.weights.WH]
theorem WXA_small : Small adder.weights.WXA := by simp [Small, adder.weights.WXA]
theorem WXB_small : Small adder.weights.WXB := by simp [Small, adder.weights.WXB]
theorem BH_small : Small adder.weights.BH := by simp [Small, adder.weights.BH]
theorem WO_small : Small adder.weights.WO := by simp [Small, adder.weights.WO]
theorem WC_small : Small adder.weights.WC := by simp [Small, adder.weights.WC]
theorem WOA_small : -127 ≤ adder.weights.WOA.val ∧ adder.weights.WOA.val ≤ 127 := by
  simp [adder.weights.WOA]
theorem WOB_small : -127 ≤ adder.weights.WOB.val ∧ adder.weights.WOB.val ≤ 127 := by
  simp [adder.weights.WOB]
theorem BO_small : -127 ≤ adder.weights.BO.val ∧ adder.weights.BO.val ≤ 127 := by
  simp [adder.weights.BO]
theorem BC_small : -127 ≤ adder.weights.BC.val ∧ adder.weights.BC.val ≤ 127 := by
  simp [adder.weights.BC]

/-! ## Lists: the facts about `RnnAdder` the loop invariants use -/

theorem dotB_drop (ws : List Int) (hs : List Bool) (i : Nat) (hw : i < ws.length)
    (hh : i < hs.length) :
    dotB (ws.drop i) (hs.drop i) =
      (if hs[i] then ws[i] else 0) + dotB (ws.drop (i + 1)) (hs.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hw, List.drop_eq_getElem_cons hh]
  rfl

theorem layer_drop (Wh : List (List Int)) (Wxa Wxb bh : List Int) (h : List Bool)
    (x : Bool × Bool) (i : Nat) (h1 : i < Wh.length) (h2 : i < Wxa.length) (h3 : i < Wxb.length)
    (h4 : i < bh.length) :
    layer (Wh.drop i) (Wxa.drop i) (Wxb.drop i) (bh.drop i) h x =
      unit Wh[i] Wxa[i] Wxb[i] bh[i] h x ::
        layer (Wh.drop (i + 1)) (Wxa.drop (i + 1)) (Wxb.drop (i + 1)) (bh.drop (i + 1)) h x := by
  rw [List.drop_eq_getElem_cons h1, List.drop_eq_getElem_cons h2, List.drop_eq_getElem_cons h3,
    List.drop_eq_getElem_cons h4]
  rfl

theorem take_set_succ {α : Type} (l : List α) (i : Nat) (v : α) (hi : i < l.length) :
    (l.set i v).take (i + 1) = l.take i ++ [v] := by
  rw [List.take_succ_eq_append_getElem (by simpa using hi), List.take_set_of_le (Nat.le_refl i)]
  simp

theorem runState_append (N : Net) (h : List Bool) (xs ys : List (Bool × Bool)) :
    runState N h (xs ++ ys) = runState N (runState N h xs) ys := by
  induction xs generalizing h with
  | nil => rfl
  | cons x xs ih => simp [runState, ih]

theorem run_append (N : Net) (h : List Bool) (xs ys : List (Bool × Bool)) :
    run N h (xs ++ ys) = run N h xs ++ run N (runState N h xs) ys := by
  induction xs generalizing h with
  | nil => rfl
  | cons x xs ih => simp [run, runState, ih]

@[simp] theorem run_length (N : Net) (h : List Bool) (xs : List (Bool × Bool)) :
    (run N h xs).length = xs.length := by
  induction xs generalizing h with
  | nil => rfl
  | cons x xs ih => simp [run, ih]

theorem bitsToNat_append (l m : List Bool) :
    bitsToNat (l ++ m) = bitsToNat l + 2 ^ l.length * bitsToNat m := by
  induction l with
  | nil => simp [bitsToNat]
  | cons b l ih => simp [bitsToNat, ih, Nat.pow_succ]; ring

theorem bitsToNat_lt (l : List Bool) : bitsToNat l < 2 ^ l.length := by
  induction l with
  | nil => simp [bitsToNat]
  | cons b l ih => cases b <;> simp [bitsToNat, Nat.pow_succ] <;> omega

/-- The low `n` bits of `x`, least significant first. -/
def bitsOf (x n : Nat) : List Bool := (List.range n).map x.testBit

theorem bitsToNat_bitsOf (x n : Nat) : bitsToNat (bitsOf x n) = x % 2 ^ n := by
  induction n with
  | zero => simp [bitsOf, bitsToNat, Nat.mod_one]
  | succ n ih =>
    have h : bitsOf x (n + 1) = bitsOf x n ++ [x.testBit n] := by
      simp [bitsOf, List.range_succ]
    rw [h, bitsToNat_append, ih, Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    have h2 : x / 2 ^ n % 2 = 0 ∨ x / 2 ^ n % 2 = 1 := by omega
    rcases h2 with h2 | h2 <;> simp [bitsOf, bitsToNat, h2]

/-- The low `n` bit pairs of `a` and `b`, least significant first: what `add_u64` feeds the
network when `n = 64`. -/
def bitPairs (a b n : Nat) : List (Bool × Bool) :=
  (List.range n).map fun j => (a.testBit j, b.testBit j)

theorem bitPairs_succ (a b n : Nat) :
    bitPairs a b (n + 1) = bitPairs a b n ++ [(a.testBit n, b.testBit n)] := by
  simp [bitPairs, List.range_succ]

@[simp] theorem bitPairs_length (a b n : Nat) : (bitPairs a b n).length = n := by
  simp [bitPairs]

theorem bitPairs_fst (a b n : Nat) : (bitPairs a b n).map Prod.fst = bitsOf a n := by
  simp [bitPairs, bitsOf]

theorem bitPairs_snd (a b n : Nat) : (bitPairs a b n).map Prod.snd = bitsOf b n := by
  simp [bitPairs, bitsOf]

/-! ## `dot_b` and `thr` -/

/-- `dot_b` returns `RnnAdder.dotB` of the same weights and state, with no overflow. -/
@[step]
theorem dot_b.spec (w : Array I32 4#usize) (h : Array Bool 4#usize) (hw : Small w) :
    adder.dot_b w h ⦃ r => r.val = dotB (ints w) h.val ∧ -508 ≤ r.val ∧ r.val ≤ 508 ⦄ := by
  unfold adder.dot_b adder.dot_b_loop
  apply loop.spec_decr_nat
    (measure := fun (s : I32 × Usize) => 4 - s.2.val)
    (inv := fun (s : I32 × Usize) =>
      s.2.val ≤ 4 ∧
      s.1.val + dotB ((ints w).drop s.2.val) (h.val.drop s.2.val) = dotB (ints w) h.val ∧
      -127 * (s.2.val : Int) ≤ s.1.val ∧ s.1.val ≤ 127 * (s.2.val : Int))
  · rintro ⟨acc, i⟩ ⟨hi, hacc, hlo, hhi⟩
    unfold adder.dot_b_loop.body
    dsimp only at hi hacc hlo hhi ⊢
    split
    · rename_i hlt
      have hi4 : i.val < 4 := by scalar_tac
      rw [dotB_drop _ _ _ (by simpa using hi4) (by simpa using hi4)] at hacc
      step as ⟨ b, hb ⟩
      split
      · rename_i hbt
        step as ⟨ x, hx ⟩
        have hxs : -127 ≤ x.val ∧ x.val ≤ 127 := hw x (by simp [hx])
        step as ⟨ acc1, hacc1 ⟩
        step as ⟨ i1, hi1 ⟩
        have hxi : (ints w)[i.val]'(by simpa using hi4) = x.val := by simp [ints, hx]
        simp only [← hb, hbt, ite_true, hxi] at hacc
        simp only [hi1]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> scalar_tac
      · rename_i hbf
        step as ⟨ i1, hi1 ⟩
        simp only [← hb, hbf] at hacc
        simp only [hi1]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> scalar_tac
    · rename_i hge
      have hi4 : i.val = 4 := by scalar_tac
      simp [hi4, dotB] at hacc hlo hhi ⊢
      exact ⟨hacc, hlo, hhi⟩
  · simp

/-- `thr` is `RnnAdder.thr`. -/
@[step]
theorem thr.spec (z : I32) : adder.thr z ⦃ r => r = thr z.val ⦄ := by
  unfold adder.thr
  simp [thr]

/-- The conditional addition of one entry of a weight array, as `step` writes it. -/
theorem cond_add_index.spec (c : Bool) (w : Array I32 4#usize) (i : Usize) (z : I32)
    (hi : i.val < 4) (hw : Small w) (hz : -1000 ≤ z.val ∧ z.val ≤ 1000) :
    (if c = true then do
        let i1 ← Array.index_usize w i
        z + i1
      else ok z) ⦃ r =>
      r.val = z.val + (if c then (ints w)[i.val]'(by simpa using hi) else 0) ∧
      z.val - 127 ≤ r.val ∧ r.val ≤ z.val + 127 ⦄ := by
  split
  · step as ⟨ x, hx ⟩
    have hxs : -127 ≤ x.val ∧ x.val ≤ 127 := hw x (by simp [hx])
    step as ⟨ r, hr ⟩
    simp [ints, hr, hx]
    scalar_tac
  · simp

/-- The conditional addition of a scalar weight, as `out` writes it. -/
theorem cond_add.spec (c : Bool) (w z : I32) (hw : -127 ≤ w.val ∧ w.val ≤ 127)
    (hz : -1000 ≤ z.val ∧ z.val ≤ 1000) :
    (if c = true then z + w else ok z) ⦃ r =>
      r.val = z.val + (if c then w.val else 0) ∧ z.val - 127 ≤ r.val ∧ r.val ≤ z.val + 127 ⦄ := by
  split
  · step as ⟨ r, hr ⟩
    simp [hr]
    scalar_tac
  · simp

/-! ## `step` -/

/-- `step` returns `RnnAdder.step` of the network read off the Rust constants. -/
theorem step.spec_rust (h : Array Bool 4#usize) (a b : Bool) :
    adder.step h a b ⦃ r => r.val = RnnAdder.step rustNet h.val (a, b) ⦄ := by
  unfold adder.step adder.step_loop
  apply loop.spec_decr_nat
    (measure := fun (s : Array Bool 4#usize × Usize) => 4 - s.2.val)
    (inv := fun (s : Array Bool 4#usize × Usize) =>
      s.2.val ≤ 4 ∧
      s.1.val.take s.2.val ++
          layer (rustNet.Wh.drop s.2.val) (rustNet.Wxa.drop s.2.val) (rustNet.Wxb.drop s.2.val)
            (rustNet.bh.drop s.2.val) h.val (a, b) =
        RnnAdder.step rustNet h.val (a, b))
  · rintro ⟨next, i⟩ ⟨hi, hinv⟩
    unfold adder.step_loop.body
    dsimp only at hi hinv ⊢
    split
    · rename_i hlt
      have hi4 : i.val < 4 := by scalar_tac
      rw [layer_drop _ _ _ _ _ _ _ (by simpa using hi4) (by simpa using hi4)
        (by simpa using hi4) (by simpa using hi4)] at hinv
      have hWXA := WXA_small
      have hWXB := WXB_small
      have hbh := BH_small (adder.weights.BH.val[i.val]'(by simpa using hi4)) (List.getElem_mem _)
      step as ⟨ row, hrow ⟩
      have hrs : Small row := WH_small row (by simp [hrow])
      step as ⟨ z, hz, hzlo, hzhi ⟩
      step with cond_add_index.spec as ⟨ z1, hz1, hz1lo, hz1hi ⟩
      step with cond_add_index.spec as ⟨ z2, hz2, hz2lo, hz2hi ⟩
      step as ⟨ x, hx ⟩
      step as ⟨ z3, hz3 ⟩
      step as ⟨ b1, hb1 ⟩
      step as ⟨ next1, hnext1 ⟩
      step as ⟨ i1, hi1 ⟩
      have hunit : b1 = unit (rustNet.Wh[i.val]'(by simpa using hi4))
          (rustNet.Wxa[i.val]'(by simpa using hi4)) (rustNet.Wxb[i.val]'(by simpa using hi4))
          (rustNet.bh[i.val]'(by simpa using hi4)) h.val (a, b) := by
        simp only [hb1, unit, hz3, hz2, hz1, hz, hx, hrow]
        simp [rustNet, ints]
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hi1, hnext1, Array.set_val_eq, take_set_succ _ _ _ (by simpa using hi4), ← hinv, ← hunit]
      simp
    · rename_i hge
      have hi4 : i.val = 4 := by scalar_tac
      simp [hi4, layer, List.drop_of_length_le, List.take_of_length_le] at hinv ⊢
      exact hinv
  · simp [RnnAdder.step]

/-- `step` returns `RnnAdder.step` on `RnnAdder.Trained.net`. -/
@[step]
theorem step.spec (h : Array Bool 4#usize) (a b : Bool) :
    adder.step h a b ⦃ r => r.val = RnnAdder.step net h.val (a, b) ⦄ := by
  rw [← rustNet_eq]
  exact step.spec_rust h a b

/-! ## `out` and `carry` -/

/-- `out` returns `RnnAdder.out` on `RnnAdder.Trained.net`. -/
@[step]
theorem out.spec (h : Array Bool 4#usize) (a b : Bool) :
    adder.out h a b ⦃ r => r = RnnAdder.out net h.val (a, b) ⦄ := by
  unfold adder.out
  have hWO := WO_small
  have hWOA := WOA_small
  have hWOB := WOB_small
  have hBO := BO_small
  step as ⟨ next, hnext ⟩
  step as ⟨ z, hz, hzlo, hzhi ⟩
  step with cond_add.spec as ⟨ z1, hz1, hz1lo, hz1hi ⟩
  step with cond_add.spec as ⟨ z2, hz2, hz2lo, hz2hi ⟩
  step as ⟨ z3, hz3 ⟩
  step as ⟨ r, hr ⟩
  rw [hr, hz3, hz2, hz1, hz, hnext, ← rustNet_eq]
  rfl

/-- `carry` returns `RnnAdder.carry` on `RnnAdder.Trained.net`. -/
@[step]
theorem carry.spec (h : Array Bool 4#usize) :
    adder.carry h ⦃ r => r = RnnAdder.carry net h.val ⦄ := by
  unfold adder.carry
  have hWC := WC_small
  have hBC := BC_small
  step as ⟨ z, hz, hzlo, hzhi ⟩
  step as ⟨ z1, hz1 ⟩
  step as ⟨ r, hr ⟩
  rw [hr, hz1, hz, ← rustNet_eq]
  rfl

/-! ## `add_bits` -/

/-- The loop of `add_bits`, started at position 0 from the initial state: it writes
`RnnAdder.run` into `sum` and ends in `RnnAdder.runState`. -/
theorem add_bits_loop.spec (xs : Slice (Bool × Bool)) (sum : Slice Bool)
    (hlen : sum.length = xs.length) :
    adder.add_bits_loop xs sum adder.weights.H0 0#usize ⦃ (sum', h') =>
      sum'.val = run net net.h0 xs.val ∧ h'.val = runState net net.h0 xs.val ⦄ := by
  unfold adder.add_bits_loop
  apply loop.spec_decr_nat
    (measure := fun (s : Slice Bool × Array Bool 4#usize × Usize) => xs.length - s.2.2.val)
    (inv := fun (s : Slice Bool × Array Bool 4#usize × Usize) =>
      s.2.2.val ≤ xs.length ∧ s.1.length = xs.length ∧
      s.1.val.take s.2.2.val ++ run net s.2.1.val (xs.val.drop s.2.2.val) =
        run net net.h0 xs.val ∧
      runState net s.2.1.val (xs.val.drop s.2.2.val) = runState net net.h0 xs.val)
  · rintro ⟨sum1, h1, i1⟩ ⟨hi, hl, hrun, hstate⟩
    unfold adder.add_bits_loop.body
    dsimp only at hi hl hrun hstate ⊢
    split
    · rename_i hlt
      have hin : i1.val < xs.length := by scalar_tac
      rw [List.drop_eq_getElem_cons (by simpa using hin)] at hrun hstate
      step as ⟨ p, hp ⟩
      rw [← hp] at hrun hstate
      obtain ⟨a, b⟩ := p
      simp only [run, runState] at hrun hstate ⊢
      step as ⟨ b1, hb1 ⟩
      step as ⟨ sum2, hsum2 ⟩
      step as ⟨ h2, hh2 ⟩
      step as ⟨ i2, hi2 ⟩
      refine ⟨by scalar_tac, by simp [hsum2, hl], ?_, ?_, by scalar_tac⟩
      · rw [hi2, hsum2, Slice.set_val_eq, take_set_succ _ _ _ (by simpa [hl] using hin), hh2,
          ← hrun, hb1]
        simp
      · rw [hi2, hh2, ← hstate]
    · rename_i hge
      have hin : i1.val = xs.length := by scalar_tac
      simp [hin, run, runState, List.take_of_length_le, ← hl] at hrun hstate ⊢
      exact ⟨hrun, hstate⟩
  · simp [H0_eq, hlen]

theorem len_eq_of_length_eq {α β : Type} {s : Slice α} {t : Slice β} (h : s.length = t.length) :
    s.len = t.len := by
  scalar_tac

/-- `add_bits` on a `sum` buffer as long as `xs`: it returns `Some` of `RnnAdder.finalCarry` and
leaves `RnnAdder.run` in `sum`. -/
theorem add_bits.spec (xs : Slice (Bool × Bool)) (sum : Slice Bool)
    (hlen : sum.length = xs.length) :
    adder.add_bits xs sum ⦃ (c, sum') =>
      c = some (finalCarry net net.h0 xs.val) ∧ sum'.val = run net net.h0 xs.val ⦄ := by
  unfold adder.add_bits
  dsimp only
  split
  · rename_i hne
    exact absurd (len_eq_of_length_eq hlen) (by simpa using hne)
  · step with add_bits_loop.spec as ⟨ sum1, h, hsum1, hh ⟩
    step as ⟨ c, hc ⟩
    simp [hc, hh, hsum1, finalCarry]

/-! ## `add_u64` -/

/-- `(a >> i) & 1 == 1` reads bit `i` of `a`. -/
theorem bit_of_shift_and (a a1 a2 : U64) (i : Nat) (h1 : a1.val = a.val >>> i)
    (h2 : a2.val = (a1 &&& 1#u64).val) : decide (a2 = 1#u64) = a.val.testBit i := by
  have h3 : a2.val = a.val / 2 ^ i % 2 := by
    rw [h2, UScalar.val_and, h1]
    simp [Nat.shiftRight_eq_div_pow]
  rw [Nat.testBit_eq_decide_div_mod_eq, ← h3, decide_eq_decide, UScalar.eq_equiv]
  simp

/-- `s |= 1 << i` under a condition, when `s` has no bit at position `i` or above. -/
theorem cond_set_bit.spec (c : Bool) (s : U64) (i : U32) (hi : i.val < 64)
    (hs : s.val < 2 ^ i.val) :
    (if c = true then do
        let i5 ← 1#u64 <<< i
        ok (s ||| i5)
      else ok s) ⦃ r => r.val = s.val + 2 ^ i.val * (if c then 1 else 0) ⦄ := by
  split
  · step as ⟨ m, hm, hmbv ⟩
    have hpow : 2 ^ i.val < U64.size := by
      have : 2 ^ i.val < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hi
      scalar_tac
    rw [UScalar.val_or, hm, Nat.one_shiftLeft, Nat.mod_eq_of_lt hpow,
      Nat.or_two_pow_eq_add_of_lt hs]
    simp
  · simp

/-- The loop of `add_u64`, from the initial state: the state ends in `RnnAdder.runState` and
`s` packs `RnnAdder.run`, both on the 64 bit pairs of `a` and `b`. -/
theorem add_u64_loop.spec (a b : U64) :
    adder.add_u64_loop a b adder.weights.H0 0#u64 0#u32 ⦃ (h', s') =>
      h'.val = runState net net.h0 (bitPairs a.val b.val 64) ∧
      s'.val = bitsToNat (run net net.h0 (bitPairs a.val b.val 64)) ⦄ := by
  unfold adder.add_u64_loop
  apply loop.spec_decr_nat
    (measure := fun (s : Array Bool 4#usize × U64 × U32) => 64 - s.2.2.val)
    (inv := fun (s : Array Bool 4#usize × U64 × U32) =>
      s.2.2.val ≤ 64 ∧
      s.1.val = runState net net.h0 (bitPairs a.val b.val s.2.2.val) ∧
      s.2.1.val = bitsToNat (run net net.h0 (bitPairs a.val b.val s.2.2.val)))
  · rintro ⟨h, s, i⟩ ⟨hi, hh, hs⟩
    unfold adder.add_u64_loop.body
    dsimp only at hi hh hs ⊢
    split
    · rename_i hlt
      have hi64 : i.val < 64 := by scalar_tac
      step as ⟨ a1, ha1, ha1bv ⟩
      step as ⟨ a2, ha2, ha2bv ⟩
      step as ⟨ b1, hb1, hb1bv ⟩
      step as ⟨ b2, hb2, hb2bv ⟩
      step as ⟨ o, ho ⟩
      rw [bit_of_shift_and a a1 a2 i.val ha1 ha2, bit_of_shift_and b b1 b2 i.val hb1 hb2] at ho ⊢
      have hslt : s.val < 2 ^ i.val := by
        rw [hs]
        simpa using bitsToNat_lt (run net net.h0 (bitPairs a.val b.val i.val))
      step with cond_set_bit.spec as ⟨ s1, hs1 ⟩
      step as ⟨ h1, hh1 ⟩
      step as ⟨ i1, hi1 ⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [hi1, bitPairs_succ, runState_append, ← hh, hh1]
        rfl
      · rw [hi1, bitPairs_succ, run_append, bitsToNat_append, ← hs, ← hh, hs1, ho]
        simp [run, bitsToNat]
    · rename_i hge
      have hi64 : i.val = 64 := by scalar_tac
      simp [hi64] at hh hs ⊢
      exact ⟨hh, hs⟩
  · simp [H0_eq, bitPairs, run, runState, bitsToNat]

/-- `add_u64` returns `RnnAdder.run`, packed, and `RnnAdder.finalCarry`, both on the 64 bit pairs
of `a` and `b`. -/
theorem add_u64.spec_net (a b : U64) :
    adder.add_u64 a b ⦃ (s, c) =>
      s.val = bitsToNat (run net net.h0 (bitPairs a.val b.val 64)) ∧
      c = finalCarry net net.h0 (bitPairs a.val b.val 64) ⦄ := by
  unfold adder.add_u64
  step with add_u64_loop.spec as ⟨ h, s, hh, hs ⟩
  step as ⟨ c, hc ⟩
  simp [hs, hc, hh, finalCarry]

/-- `add_u64` is 64-bit addition with its carry out, by `RnnAdder.Trained.adds`. -/
theorem add_u64.spec (a b : U64) :
    adder.add_u64 a b ⦃ (s, c) =>
      s.val = (a.val + b.val) % 2 ^ 64 ∧ c = decide (a.val + b.val ≥ 2 ^ 64) ⦄ := by
  apply WP.spec_mono (add_u64.spec_net a b)
  rintro ⟨s, c⟩ ⟨hs, hc⟩
  have hadds := RnnAdder.Trained.adds (bitPairs a.val b.val 64)
  have ha : a.val < 2 ^ 64 := by scalar_tac
  have hb : b.val < 2 ^ 64 := by scalar_tac
  have hslt : s.val < 2 ^ 64 := by scalar_tac
  rw [← hs, ← hc, bitPairs_fst, bitPairs_snd, bitsToNat_bitsOf, bitsToNat_bitsOf, bitPairs_length,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hadds
  show s.val = (a.val + b.val) % 2 ^ 64 ∧ c = decide (a.val + b.val ≥ 2 ^ 64)
  cases c <;> simp at hadds ⊢ <;> omega

/-! ## Gate 1A: the theorems the gates check

Each says that a translated function equals `ok` of a value, for every argument. `adder.step`
returns an array and `adder.add_bits` a slice, so their theorems name the returned value by an
existential and state its contents as a list (`Array.val`, `Slice.val`); an array or a slice is
determined by that list (`Array.ext`, `Slice.ext`). -/

/-- `step` returns `ok` of `RnnAdder.step` on `RnnAdder.Trained.net`, for every state and input.
The Rust state `[bool; 4]` is read as the list `h.val`. -/
theorem step_eq (h : Array Bool 4#usize) (a b : Bool) :
    ∃ r, adder.step h a b = ok r ∧ r.val = RnnAdder.step RnnAdder.Trained.net h.val (a, b) :=
  eq_ok_of_spec (step.spec h a b)

/-- `out` returns `ok` of `RnnAdder.out` on `RnnAdder.Trained.net`, for every state and input. -/
theorem out_eq (h : Array Bool 4#usize) (a b : Bool) :
    adder.out h a b = ok (RnnAdder.out RnnAdder.Trained.net h.val (a, b)) := by
  obtain ⟨v, hv, hp⟩ := eq_ok_of_spec (out.spec h a b)
  rw [hv, hp]

/-- `carry` returns `ok` of `RnnAdder.carry` on `RnnAdder.Trained.net`, for every state. -/
theorem carry_eq (h : Array Bool 4#usize) :
    adder.carry h = ok (RnnAdder.carry RnnAdder.Trained.net h.val) := by
  obtain ⟨v, hv, hp⟩ := eq_ok_of_spec (carry.spec h)
  rw [hv, hp]

/-- `add_bits` when `sum` is as long as `xs`, for every length: it returns `ok` of `Some` of
`RnnAdder.finalCarry` and of the updated `sum`, which is `RnnAdder.run`. -/
theorem add_bits_eq (xs : Slice (Bool × Bool)) (sum : Slice Bool)
    (hlen : sum.length = xs.length) :
    ∃ sum', adder.add_bits xs sum =
        ok (some (RnnAdder.finalCarry RnnAdder.Trained.net RnnAdder.Trained.net.h0 xs.val), sum') ∧
      sum'.val = RnnAdder.run RnnAdder.Trained.net RnnAdder.Trained.net.h0 xs.val := by
  obtain ⟨⟨c, sum'⟩, hv, hc, hsum⟩ := eq_ok_of_spec (add_bits.spec xs sum hlen)
  exact ⟨sum', by rw [hv, hc], hsum⟩

/-- `add_bits` when the lengths differ: it returns `ok` of `None` and of `sum` unchanged. -/
theorem add_bits_len_ne (xs : Slice (Bool × Bool)) (sum : Slice Bool)
    (hlen : sum.length ≠ xs.length) :
    adder.add_bits xs sum = ok (none, sum) := by
  unfold adder.add_bits
  dsimp only
  split
  · rfl
  · rename_i heq
    exact absurd (by simpa using heq) hlen

/-- `add_bits` when `sum` is as long as `xs`, composed with `RnnAdder.Trained.sums_correct` and
`RnnAdder.Trained.carry_correct`: the result is the ripple-carry adder's. -/
theorem add_bits_ripple (xs : Slice (Bool × Bool)) (sum : Slice Bool)
    (hlen : sum.length = xs.length) :
    ∃ sum', adder.add_bits xs sum = ok (some (RnnAdder.carryOut false xs.val), sum') ∧
      sum'.val = RnnAdder.addBits false xs.val := by
  obtain ⟨sum', hv, hsum⟩ := add_bits_eq xs sum hlen
  rw [RnnAdder.Trained.carry_correct] at hv
  rw [RnnAdder.Trained.sums_correct] at hsum
  exact ⟨sum', hv, hsum⟩

/-- `add_bits` when `sum` is as long as `xs`, composed with `RnnAdder.Trained.adds`: the number
the updated `sum` spells, plus the returned carry at position `xs.length`, is the sum of the two
input numbers. -/
theorem add_bits_adds (xs : Slice (Bool × Bool)) (sum : Slice Bool)
    (hlen : sum.length = xs.length) :
    ∃ c sum', adder.add_bits xs sum = ok (some c, sum') ∧
      RnnAdder.bitsToNat sum'.val + 2 ^ xs.length * (if c then 1 else 0) =
        RnnAdder.bitsToNat (xs.val.map Prod.fst) + RnnAdder.bitsToNat (xs.val.map Prod.snd) := by
  obtain ⟨sum', hv, hsum⟩ := add_bits_eq xs sum hlen
  exact ⟨_, sum', hv, by rw [hsum]; exact RnnAdder.Trained.adds xs.val⟩

/-- `add_u64` returns `ok` of `RnnAdder.run`, packed into a `u64`, and of `RnnAdder.finalCarry`,
both on the 64 bit pairs of `a` and `b`, for all `a` and `b`. -/
theorem add_u64_net_eq (a b : U64) :
    ∃ s c, adder.add_u64 a b = ok (s, c) ∧
      s.val = RnnAdder.bitsToNat (RnnAdder.run RnnAdder.Trained.net RnnAdder.Trained.net.h0
        (bitPairs a.val b.val 64)) ∧
      c = RnnAdder.finalCarry RnnAdder.Trained.net RnnAdder.Trained.net.h0
        (bitPairs a.val b.val 64) := by
  obtain ⟨⟨s, c⟩, hv, hs, hc⟩ := eq_ok_of_spec (add_u64.spec_net a b)
  exact ⟨s, c, hv, hs, hc⟩

/-- `add_u64` returns `ok` of the sum modulo `2^64` and of the carry out, for all `a` and `b`. -/
theorem add_u64_eq (a b : U64) :
    ∃ s c, adder.add_u64 a b = ok (s, c) ∧ s.val = (a.val + b.val) % 2 ^ 64 ∧
      c = decide (a.val + b.val ≥ 2 ^ 64) := by
  obtain ⟨⟨s, c⟩, hv, hs, hc⟩ := eq_ok_of_spec (add_u64.spec a b)
  exact ⟨s, c, hv, hs, hc⟩

end LcnExec.Adder
