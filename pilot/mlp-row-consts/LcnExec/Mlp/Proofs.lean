import LcnExec.Translated.Mlp
import LeanCheckedNetwork.Trained.Weights

/-! PILOT, not a gate: the MLP of `rust/mlp`, proved against a variant of the crate.

`rust/mlp/src/weights.rs` writes each table as one array literal of 113 rows of 128 entries.
Aeneas translates that to one Lean definition with 14,464 scalar literals, and Lean does not
elaborate it (evidence/mlp/pilot/). `scripts/mlp_row_consts.py` writes the same tables with one
`const` per row; `src/lib.rs` is untouched and its nine translated definitions come out
identical. `scripts/mlp_pilot.sh` builds that variant in a scratch tree, translates it, and builds
this file there as `LcnExec.Mlp.Proofs`. The theorems below are therefore about the translation
of the variant, not about `rust/mlp` as it is.

What is proved: on the translated functions, `predict a b` returns `ok (some c)` with `c` the
answer of `LeanCheckedNetwork.answer` on the tables of `LeanCheckedNetwork.Trained`, for
`a, b < 113`, and `ok none` otherwise. The table entries reach the theorem through the
translation of `weights.rs` (`E1_eq`, `E2_eq`, `W2_eq`); no entry is written in this file.
`LcnExec/Mlp/AddsMod113.lean` composes this with `LeanCheckedNetwork.Trained.adds_mod_113`. -/

open Aeneas Aeneas.Std Result ControlFlow

namespace LcnExec.Mlp

open LeanCheckedNetwork (nth hidden dot scores argmaxFrom argmax answer)

/-- A total-correctness triple pins the computation down: it is `ok v` for some `v` satisfying
the postcondition. The same lemma as `LcnExec.Adder.eq_ok_of_spec`. -/
theorem eq_ok_of_spec {α : Type} {m : Result α} {p : α → Prop} (h : m ⦃ x => p x ⦄) :
    ∃ v, m = ok v ∧ p v := by
  cases m with
  | ret r => exact ⟨r, rfl, by simpa using h⟩
  | vis i k => simp at h
  | div => simp at h

/-! ## The tables -/

/-- The integer values of a row of `i8`. -/
def ints8 {n : Usize} (r : Array I8 n) : List Int := r.val.map (·.val)

@[simp] theorem ints8_length {n : Usize} (r : Array I8 n) : (ints8 r).length = n.val := by
  simp [ints8]

/-- A table of `i8` as a list of rows of integers. -/
def tableInts {n m : Usize} (t : Array (Array I8 m) n) : List (List Int) := t.val.map ints8

@[simp] theorem tableInts_length {n m : Usize} (t : Array (Array I8 m) n) :
    (tableInts t).length = n.val := by
  simp [tableInts]

@[simp, scalar_tac_simps]
theorem HID_val : mlp.weights.HID.val = 128 := by simp [mlp.weights.HID]

@[simp, scalar_tac_simps]
theorem P_val : mlp.weights.P.val = 113 := by simp [mlp.weights.P]

/-! ## Lists -/

theorem nth_eq_getElem (t : List (List Int)) (n : Nat) (h : n < t.length) : nth t n = t[n] := by
  induction t generalizing n with
  | nil => simp at h
  | cons r rs ih =>
    cases n with
    | zero => rfl
    | succ n => simpa [nth] using ih n (by simpa using h)

theorem hidden_drop (xs ys : List Int) (k : Nat) (hx : k < xs.length) (hy : k < ys.length) :
    hidden (xs.drop k) (ys.drop k) =
      (xs[k] + ys[k]) * (xs[k] + ys[k]) :: hidden (xs.drop (k + 1)) (ys.drop (k + 1)) := by
  rw [List.drop_eq_getElem_cons hx, List.drop_eq_getElem_cons hy]
  rfl

theorem dot_drop (xs ys : List Int) (k : Nat) (hx : k < xs.length) (hy : k < ys.length) :
    dot (xs.drop k) (ys.drop k) = xs[k] * ys[k] + dot (xs.drop (k + 1)) (ys.drop (k + 1)) := by
  rw [List.drop_eq_getElem_cons hx, List.drop_eq_getElem_cons hy]
  rfl

theorem scores_drop (h : List Int) (W : List (List Int)) (c : Nat) (hc : c < W.length) :
    scores h (W.drop c) = dot W[c] h :: scores h (W.drop (c + 1)) := by
  rw [List.drop_eq_getElem_cons hc]
  rfl

theorem take_set_succ {α : Type} (l : List α) (i : Nat) (v : α) (hi : i < l.length) :
    (l.set i v).take (i + 1) = l.take i ++ [v] := by
  rw [List.take_succ_eq_append_getElem (by simpa using hi), List.take_set_of_le (Nat.le_refl i)]
  simp

theorem sq_bound (s : Int) (h : -256 ≤ s ∧ s ≤ 254) : 0 ≤ s * s ∧ s * s ≤ 65536 := by
  constructor <;> nlinarith [h.1, h.2]

theorem mul_bound (x y : Int) (hx : -128 ≤ x ∧ x ≤ 127) (hy : 0 ≤ y ∧ y ≤ 65536) :
    -8388608 ≤ x * y ∧ x * y ≤ 8388608 := by
  constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

/-! ## `hidden` -/

/-- `hidden` returns `LeanCheckedNetwork.hidden` of row `a` of `E1` and row `b` of `E2`; every
entry is a square of a sum of two `i8`, so it is in `[0, 65536]`. -/
@[step]
theorem hidden.spec (a b : Usize) (ha : a.val < 113) (hb : b.val < 113) :
    mlp.hidden a b ⦃ h =>
      h.val.map (·.val) =
        hidden (ints8 (mlp.weights.E1.val[a.val]'(by simpa using ha)))
          (ints8 (mlp.weights.E2.val[b.val]'(by simpa using hb))) ∧
      ∀ x ∈ h.val, 0 ≤ x.val ∧ x.val ≤ 65536 ⦄ := by
  unfold mlp.hidden mlp.hidden_loop
  generalize hr1 : ints8 (mlp.weights.E1.val[a.val]'(by simpa using ha)) = r1
  generalize hr2 : ints8 (mlp.weights.E2.val[b.val]'(by simpa using hb)) = r2
  have hl1 : r1.length = 128 := by simp [← hr1]
  have hl2 : r2.length = 128 := by simp [← hr2]
  apply loop.spec_decr_nat
    (measure := fun (s : Array I32 128#usize × Usize) => 128 - s.2.val)
    (inv := fun (s : Array I32 128#usize × Usize) =>
      s.2.val ≤ 128 ∧
      (s.1.val.take s.2.val).map (·.val) ++ hidden (r1.drop s.2.val) (r2.drop s.2.val) =
        hidden r1 r2 ∧
      ∀ x ∈ s.1.val, 0 ≤ x.val ∧ x.val ≤ 65536)
  · rintro ⟨h, k⟩ ⟨hk, hinv, hbnd⟩
    unfold mlp.hidden_loop.body
    dsimp only at hk hinv hbnd ⊢
    split
    · rename_i hlt
      have hk128 : k.val < 128 := by scalar_tac
      rw [hidden_drop _ _ _ (by omega) (by omega)] at hinv
      step as ⟨ row1, hrow1 ⟩
      step as ⟨ x1, hx1 ⟩
      step with IScalar.cast_inBounds_spec as ⟨ y1, hy1 ⟩
      step as ⟨ row2, hrow2 ⟩
      step as ⟨ x2, hx2 ⟩
      step with IScalar.cast_inBounds_spec as ⟨ y2, hy2 ⟩
      step as ⟨ s, hs ⟩
      have hsq := sq_bound s.val (by scalar_tac)
      step as ⟨ q, hq ⟩
      step as ⟨ h1, hh1 ⟩
      step as ⟨ k1, hk1 ⟩
      have hr1k : r1[k.val]'(by omega) = x1.val := by simp [← hr1, ints8, hx1, hrow1]
      have hr2k : r2[k.val]'(by omega) = x2.val := by simp [← hr2, ints8, hx2, hrow2]
      have hqv : q.val = (r1[k.val]'(by omega) + r2[k.val]'(by omega)) *
          (r1[k.val]'(by omega) + r2[k.val]'(by omega)) := by
        rw [hq, hs, hy1, hy2, hr1k, hr2k]
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [hk1, hh1, Array.set_val_eq, take_set_succ _ _ _ (by simpa using hk128), ← hinv]
        simp [hqv]
      · intro x hx
        rw [hh1, Array.set_val_eq] at hx
        rcases List.mem_or_eq_of_mem_set hx with hx | hx
        · exact hbnd x hx
        · rw [hx, hq]
          exact hsq
    · rename_i hge
      have hk128 : k.val = 128 := by scalar_tac
      simp [hk128, LeanCheckedNetwork.hidden, List.drop_of_length_le, List.take_of_length_le, hl1,
        hl2] at hinv ⊢
      exact ⟨hinv, hbnd⟩
  · simp

/-! ## `score` -/

/-- `score` returns `LeanCheckedNetwork.dot` of row `c` of `W2` with the hidden layer. -/
@[step]
theorem score.spec (h : Array I32 128#usize) (c : Usize) (hc : c.val < 113)
    (hh : ∀ x ∈ h.val, 0 ≤ x.val ∧ x.val ≤ 65536) :
    mlp.score h c ⦃ r =>
      r.val = dot (ints8 (mlp.weights.W2.val[c.val]'(by simpa using hc))) (h.val.map (·.val)) ⦄ := by
  unfold mlp.score mlp.score_loop
  generalize hw : ints8 (mlp.weights.W2.val[c.val]'(by simpa using hc)) = w
  generalize hhI : h.val.map (·.val) = hI
  have hlw : w.length = 128 := by simp [← hw]
  have hlh : hI.length = 128 := by simp [← hhI]
  apply loop.spec_decr_nat
    (measure := fun (s : I64 × Usize) => 128 - s.2.val)
    (inv := fun (s : I64 × Usize) =>
      s.2.val ≤ 128 ∧
      s.1.val + dot (w.drop s.2.val) (hI.drop s.2.val) = dot w hI ∧
      -8388608 * (s.2.val : Int) ≤ s.1.val ∧ s.1.val ≤ 8388608 * (s.2.val : Int))
  · rintro ⟨acc, k⟩ ⟨hk, hacc, hlo, hhi⟩
    unfold mlp.score_loop.body
    dsimp only at hk hacc hlo hhi ⊢
    split
    · rename_i hlt
      have hk128 : k.val < 128 := by scalar_tac
      rw [dot_drop _ _ _ (by omega) (by omega)] at hacc
      step as ⟨ row, hrow ⟩
      step as ⟨ x, hx ⟩
      step with IScalar.cast_inBounds_spec as ⟨ x64, hx64 ⟩
      step as ⟨ y, hy ⟩
      have hyb := hh y (by simp [hy])
      step with IScalar.cast_inBounds_spec as ⟨ y64, hy64 ⟩
      have hprod := mul_bound x64.val y64.val (by scalar_tac) (by scalar_tac)
      step as ⟨ p, hp ⟩
      step as ⟨ acc1, hacc1 ⟩
      step as ⟨ k1, hk1 ⟩
      have hwk : w[k.val]'(by omega) = x.val := by simp [← hw, ints8, hx, hrow]
      have hhk : hI[k.val]'(by omega) = y.val := by simp [← hhI, hy]
      rw [hwk, hhk, ← hx64, ← hy64, ← hp] at hacc
      simp only [hk1]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> scalar_tac
    · rename_i hge
      have hk128 : k.val = 128 := by scalar_tac
      simp [hk128, dot, List.drop_of_length_le, hlw, hlh] at hacc ⊢
      exact hacc
  · simp

/-! ## `predict` -/

/-- The loop of `predict`: from candidate `c` on, with the best index and score so far, it
returns `LeanCheckedNetwork.argmaxFrom` over the remaining scores. -/
theorem predict_loop.spec (h : Array I32 128#usize)
    (hh : ∀ x ∈ h.val, 0 ≤ x.val ∧ x.val ≤ 65536) (best : Usize) (best_score : I64) (c : Usize)
    (hc : c.val ≤ 113) :
    mlp.predict_loop h best best_score c ⦃ r =>
      r.val = argmaxFrom (scores (h.val.map (·.val)) ((tableInts mlp.weights.W2).drop c.val))
        c.val best.val best_score.val ⦄ := by
  unfold mlp.predict_loop
  generalize hhI : h.val.map (·.val) = hI
  generalize hW : tableInts mlp.weights.W2 = W
  have hlW : W.length = 113 := by simp [← hW]
  apply loop.spec_decr_nat
    (measure := fun (s : Usize × I64 × Usize) => 113 - s.2.2.val)
    (inv := fun (s : Usize × I64 × Usize) =>
      s.2.2.val ≤ 113 ∧
      argmaxFrom (scores hI (W.drop s.2.2.val)) s.2.2.val s.1.val s.2.1.val =
        argmaxFrom (scores hI (W.drop c.val)) c.val best.val best_score.val)
  · rintro ⟨best1, bs1, c1⟩ ⟨hc1, hinv⟩
    unfold mlp.predict_loop.body
    dsimp only at hc1 hinv ⊢
    split
    · rename_i hlt
      have hc113 : c1.val < 113 := by scalar_tac
      rw [scores_drop _ _ _ (by omega)] at hinv
      step as ⟨ s, hs ⟩
      have hs' : s.val = dot (W[c1.val]'(by omega)) hI := by
        simp [hs, ← hW, ← hhI, tableInts]
      simp only [argmaxFrom, ← hs'] at hinv
      split
      · rename_i hgt
        have hlt' : bs1.val < s.val := by scalar_tac
        simp only [hlt', ite_true] at hinv
        step as ⟨ c2, hc2 ⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hc2]
        exact hinv
      · rename_i hle
        have hlt' : ¬ bs1.val < s.val := by scalar_tac
        simp only [hlt', ite_false] at hinv
        step as ⟨ c2, hc2 ⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hc2]
        exact hinv
    · rename_i hge
      have hc113 : c1.val = 113 := by scalar_tac
      simp [hc113, scores, argmaxFrom, List.drop_of_length_le, hlW] at hinv ⊢
      exact hinv
  · exact ⟨hc, rfl⟩

/-- `predict` on an in-range pair returns `Some` of `LeanCheckedNetwork.answer` on the tables
read off the translated Rust statics. -/
theorem predict.spec (a b : Usize) (ha : a.val < 113) (hb : b.val < 113) :
    mlp.predict a b ⦃ r => ∃ c, r = some c ∧
      c.val = answer (tableInts mlp.weights.E1) (tableInts mlp.weights.E2)
        (tableInts mlp.weights.W2) a.val b.val ⦄ := by
  unfold mlp.predict
  split
  · rename_i hge
    exact absurd hge (by scalar_tac)
  · split
    · rename_i hge
      exact absurd hge (by scalar_tac)
    · step as ⟨ h, hh, hbnd ⟩
      step as ⟨ s0, hs0 ⟩
      step with predict_loop.spec as ⟨ best, hbest ⟩
      refine ⟨best, rfl, ?_⟩
      have hnth1 : nth (tableInts mlp.weights.E1) a.val =
          ints8 (mlp.weights.E1.val[a.val]'(by simpa using ha)) := by
        rw [nth_eq_getElem _ _ (by simpa using ha)]
        simp [tableInts]
      have hnth2 : nth (tableInts mlp.weights.E2) b.val =
          ints8 (mlp.weights.E2.val[b.val]'(by simpa using hb)) := by
        rw [nth_eq_getElem _ _ (by simpa using hb)]
        simp [tableInts]
      have hsc := scores_drop (h.val.map (·.val)) (tableInts mlp.weights.W2) 0 (by simp)
      rw [List.drop_zero] at hsc
      have hW0 : (tableInts mlp.weights.W2)[0]'(by simp) =
          ints8 (mlp.weights.W2.val[0]'(by simp)) := by
        simp [tableInts]
      unfold LeanCheckedNetwork.answer
      rw [hnth1, hnth2, ← hh, hsc, hbest, hs0, hW0]
      rfl

/-- `predict` on a pair out of range returns `None`. -/
theorem predict_out_of_range (a b : Usize) (h : ¬ (a.val < 113 ∧ b.val < 113)) :
    mlp.predict a b = ok none := by
  unfold mlp.predict
  split
  · rfl
  · split
    · rfl
    · rename_i h1 h2
      exact absurd ⟨by scalar_tac, by scalar_tac⟩ h

/-! ## The tables of the translation are the tables of `LeanCheckedNetwork.Trained` -/

/-- Peels `Array.make` off a row, leaving the list of scalar literals for the kernel to read. -/
theorem ints8_make (n : Usize) (l : List I8) (h : l.length = n.val) :
    ints8 (Array.make n l h) = l.map (·.val) := by
  simp [ints8]

set_option maxRecDepth 100000 in
theorem E1_eq : tableInts mlp.weights.E1 = LeanCheckedNetwork.Trained.E1 := by
  simp only [tableInts, mlp.weights.E1, Array.make_val, List.map_cons, List.map_nil, global_simps,
    ints8_make]
  decide +kernel

set_option maxRecDepth 100000 in
theorem E2_eq : tableInts mlp.weights.E2 = LeanCheckedNetwork.Trained.E2 := by
  simp only [tableInts, mlp.weights.E2, Array.make_val, List.map_cons, List.map_nil, global_simps,
    ints8_make]
  decide +kernel

set_option maxRecDepth 100000 in
theorem W2_eq : tableInts mlp.weights.W2 = LeanCheckedNetwork.Trained.W2 := by
  simp only [tableInts, mlp.weights.W2, Array.make_val, List.map_cons, List.map_nil, global_simps,
    ints8_make]
  decide +kernel

/-! ## The refinement theorem, as an equation -/

/-- `predict` on an in-range pair returns `ok` of `Some` of the answer of the Lean network
`LeanCheckedNetwork.Trained.answer`. -/
theorem predict_eq (a b : Usize) (ha : a.val < 113) (hb : b.val < 113) :
    ∃ c, mlp.predict a b = ok (some c) ∧ c.val = LeanCheckedNetwork.Trained.answer a.val b.val := by
  obtain ⟨r, hr, c, hrc, hc⟩ := eq_ok_of_spec (predict.spec a b ha hb)
  refine ⟨c, by rw [hr, hrc], ?_⟩
  rw [hc, E1_eq, E2_eq, W2_eq]
  rfl

end LcnExec.Mlp
