import LcnExec.GeneralEngine.View

open Aeneas Aeneas.Std Result ControlFlow
namespace LcnExec.GeneralEngine

/-! ## The score dot, the projections, the embedding, the row read and the exponential

Ports of the one-layer engine stage proofs to the translated `general_engine` functions,
with the same loop invariants and the same frozen envelopes. -/

/-- The bound is above both query and key bounds of the accepted load box. -/
def Small (x : Array I64 32#usize) : Prop :=
  ∀ v ∈ x.val, -1000000 ≤ v.val ∧ v.val ≤ 1000000

theorem dot_drop (xs ys : List Int) (i : Nat) (hx : i < xs.length) (hy : i < ys.length) :
    GeneralModel.dot (xs.drop i) (ys.drop i) =
      xs[i] * ys[i] + GeneralModel.dot (xs.drop (i + 1)) (ys.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hx, List.drop_eq_getElem_cons hy]
  rfl

theorem mul_bound (x y : Int) (hx : -1000000 ≤ x ∧ x ≤ 1000000)
    (hy : -1000000 ≤ y ∧ y ≤ 1000000) :
    -1000000000000 ≤ x * y ∧ x * y ≤ 1000000000000 := by
  constructor <;> nlinarith [mul_nonneg (by omega : 0 ≤ x + 1000000) (by omega : 0 ≤ y + 1000000),
    mul_nonneg (by omega : 0 ≤ 1000000 - x) (by omega : 0 ≤ 1000000 - y),
    mul_nonneg (by omega : 0 ≤ x + 1000000) (by omega : 0 ≤ 1000000 - y),
    mul_nonneg (by omega : 0 ≤ 1000000 - x) (by omega : 0 ≤ y + 1000000)]

/-- Total correctness of the real Rust score dot loop, for arbitrary bounded vectors. -/
theorem dot_spec (x y : Array I64 32#usize) (hx : Small x) (hy : Small y) :
    general_engine.dot x y ⦃ r => r.val = GeneralModel.dot (ints x) (ints y) ⦄ := by
  unfold general_engine.dot general_engine.dot_loop
  apply loop.spec_decr_nat
    (measure := fun (s : I64 × Usize) => 32 - s.2.val)
    (inv := fun (s : I64 × Usize) =>
      s.2.val ≤ 32 ∧
      s.1.val + GeneralModel.dot ((ints x).drop s.2.val) ((ints y).drop s.2.val) =
        GeneralModel.dot (ints x) (ints y) ∧
      -1000000000000 * (s.2.val : Int) ≤ s.1.val ∧
      s.1.val ≤ 1000000000000 * (s.2.val : Int))
  · rintro ⟨acc, i⟩ ⟨hi, hacc, hlo, hhi⟩
    unfold general_engine.dot_loop.body
    dsimp only at hi hacc hlo hhi ⊢
    simp only [general_engine.D_HEAD]
    split
    · rename_i hlt
      have hi32 : i.val < 32 := by scalar_tac
      rw [dot_drop _ _ _ (by simpa [ints] using hi32) (by simpa [ints] using hi32)] at hacc
      step as ⟨xv, hxv⟩
      step as ⟨yv, hyv⟩
      have hxs := hx xv (by simp [hxv])
      have hys := hy yv (by simp [hyv])
      have hp := mul_bound xv.val yv.val hxs hys
      step as ⟨p, hpv⟩
      step as ⟨acc1, hacc1⟩
      step as ⟨i1, hi1⟩
      have hxi : (ints x)[i.val]'(by simpa [ints] using hi32) = xv.val := by
        simp [ints, hxv]
      have hyi : (ints y)[i.val]'(by simpa [ints] using hi32) = yv.val := by
        simp [ints, hyv]
      rw [hxi, hyi] at hacc
      simp only [hi1]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> scalar_tac
    · have hi32 : i.val = 32 := by scalar_tac
      simpa [hi32, ints, GeneralModel.dot] using hacc
  · simp

/-- The returned result is `ok`, not a failure or divergence, and its integer is the model dot. -/
theorem dot_eq (x y : Array I64 32#usize) (hx : Small x) (hy : Small y) :
    ∃ r, general_engine.dot x y = ok r ∧ r.val = GeneralModel.dot (ints x) (ints y) := by
  have h := dot_spec x y hx hy
  cases heq : general_engine.dot x y with
  | ret r => exact ⟨r, rfl, by simpa [heq] using h⟩
  | vis i k => simp [heq] at h
  | div => simp [heq] at h

theorem project_nth_eq {α : Type} (d : α) (xs : List α) (i : Nat) (h : i < xs.length) :
    GeneralModel.nth d xs i = xs[i] := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa using h)

theorem project_mul_bound (x y bx bw : Int) (_hbx : 0 ≤ bx) (_hbw : 0 ≤ bw)
    (hx : -bx ≤ x ∧ x ≤ bx) (hy : -bw ≤ y ∧ y ≤ bw) :
    -(bx * bw) ≤ x * y ∧ x * y ≤ bx * bw := by
  constructor <;> nlinarith [mul_nonneg (by omega : 0 ≤ x + bx) (by omega : 0 ≤ y + bw),
    mul_nonneg (by omega : 0 ≤ bx - x) (by omega : 0 ≤ bw - y),
    mul_nonneg (by omega : 0 ≤ x + bx) (by omega : 0 ≤ bw - y),
    mul_nonneg (by omega : 0 ≤ bx - x) (by omega : 0 ≤ y + bw)]

def project_column (w : Array (Array I8 32#usize) 128#usize) (i : Nat) : List Int :=
  w.val.map (fun row => GeneralModel.nth 0 (row.val.map (·.val)) i)

/-- Total correctness and the prefix envelope of the translated contraction loop. -/
theorem project_inner_spec (x : Array I64 128#usize)
    (w : Array (Array I8 32#usize) 128#usize) (i : Usize)
    (bx bw : Int) (hi : i.val < 32) (hbx : 0 ≤ bx) (hbw : 0 ≤ bw)
    (hx : Bounded bx x) (hw : MatrixBound bw w)
    (henv : 128 * bx * bw ≤ Envelope.value) :
    general_engine.project_loop0_loop0 x w i 0#i64 0#usize ⦃ r =>
      r.val = GeneralModel.dot (ints x) (project_column w i.val) ∧
      -(128 * bx * bw) ≤ r.val ∧ r.val ≤ 128 * bx * bw ⦄ := by
  have hb : 0 ≤ bx * bw := mul_nonneg hbx hbw
  change 128 * bx * bw ≤ 1723136 at henv
  have hprod : bx * bw ≤ 1723136 := by nlinarith
  unfold general_engine.project_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (s : I64 × Usize) => 128 - s.2.val)
    (inv := fun (s : I64 × Usize) =>
      s.2.val ≤ 128 ∧
      s.1.val + GeneralModel.dot ((ints x).drop s.2.val)
        ((project_column w i.val).drop s.2.val) =
        GeneralModel.dot (ints x) (project_column w i.val) ∧
      -(s.2.val : Int) * (bx * bw) ≤ s.1.val ∧
      s.1.val ≤ (s.2.val : Int) * (bx * bw))
  · rintro ⟨acc, k⟩ ⟨hk, hacc, hlo, hhi⟩
    unfold general_engine.project_loop0_loop0.body
    dsimp only at hk hacc hlo hhi ⊢
    simp only [general_engine.D_MODEL]
    split
    · have hk128 : k.val < 128 := by scalar_tac
      have hkp : (k.val : Int) * (bx * bw) ≤ 128 * bx * bw := by
        have : (k.val : Int) ≤ 128 := by omega
        nlinarith
      have hk1p : ((k.val : Int) + 1) * (bx * bw) ≤ 128 * bx * bw := by
        have : (k.val : Int) + 1 ≤ 128 := by omega
        nlinarith
      rw [dot_drop _ _ _ (by simpa [ints] using hk128)
        (by simpa [project_column] using hk128)] at hacc
      step as ⟨xv, hxv⟩
      step as ⟨row, hrow⟩
      step as ⟨wv, hwv⟩
      have hxs := hx xv (by simp [hxv])
      have hws := hw row (by simp [hrow]) wv (by simp [hwv])
      have hp := project_mul_bound xv.val wv.val bx bw hbx hbw hxs hws
      step as ⟨wv64, hwv64⟩
      step as ⟨p, hpv⟩
      step as ⟨acc1, hacc1⟩
      step as ⟨k1, hk1⟩
      have hxi : (ints x)[k.val]'(by simpa [ints] using hk128) = xv.val := by
        simp [ints, hxv]
      have hwi : (project_column w i.val)[k.val]'(by simpa [project_column] using hk128) = wv.val := by
        simp [project_column, hrow, project_nth_eq, hi, hwv]
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
      simpa [hk128, ints, project_column, GeneralModel.dot, mul_assoc] using
        And.intro hacc (And.intro hlo hhi)
  · simp

theorem project_addV_length (xs ys : List Int) (h : xs.length = ys.length) :
    (GeneralModel.addV xs ys).length = xs.length := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys => simpa [GeneralModel.addV] using ih ys (by simpa using h)

theorem project_addV_get (xs ys : List Int) (h : xs.length = ys.length)
    (i : Nat) (hi : i < xs.length) :
    (GeneralModel.addV xs ys)[i]'(by rw [project_addV_length xs ys h]; exact hi) =
      xs[i] + ys[i]'(by omega) := by
  induction xs generalizing ys i with
  | nil => simp at hi
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i => exact ih ys (by simpa using h) i (by simpa using hi)

theorem project_scale_eq (c : Int) (xs : List Int) :
    GeneralModel.scale c xs = xs.map (fun x => c * x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [GeneralModel.scale, ih]

theorem project_lincomb_length (n : Nat) (xs : List Int) (ws : List (List Int))
    (hw : ∀ row ∈ ws, row.length = n) :
    (GeneralModel.lincomb n xs ws).length = n := by
  induction xs generalizing ws with
  | nil => simp [GeneralModel.lincomb]
  | cons x xs ih =>
    cases ws with
    | nil => simp [GeneralModel.lincomb]
    | cons row ws =>
      have hr := hw row (by simp)
      have hs := ih ws (by intro r h; exact hw r (by simp [h]))
      simp only [GeneralModel.lincomb]
      rw [project_addV_length _ _ (by simpa [project_scale_eq] using hr.trans hs.symm)]
      simpa [project_scale_eq] using hr

theorem project_lincomb_get (n : Nat) (xs : List Int) (ws : List (List Int))
    (hw : ∀ row ∈ ws, row.length = n) (i : Nat) (hi : i < n) :
    (GeneralModel.lincomb n xs ws)[i]'(by rw [project_lincomb_length n xs ws hw]; exact hi) =
      GeneralModel.dot xs (ws.map (fun row => GeneralModel.nth 0 row i)) := by
  induction xs generalizing ws with
  | nil => simp [GeneralModel.lincomb, GeneralModel.dot]
  | cons x xs ih =>
    cases ws with
    | nil => simp [GeneralModel.lincomb, GeneralModel.dot]
    | cons row ws =>
      have hr := hw row (by simp)
      have hws : ∀ r ∈ ws, r.length = n := by intro r h; exact hw r (by simp [h])
      have hs := project_lincomb_length n xs ws hws
      simp only [GeneralModel.lincomb]
      rw [project_addV_get _ _ (by simp [project_scale_eq, hr, hs]) i (by simp [project_scale_eq, hr, hi])]
      simp [project_scale_eq, project_nth_eq, hr, hi, ih ws hws, GeneralModel.dot]

theorem project_bounded_set {n : Usize} (b : Int) (x : Array I64 n)
    (i : Usize) (v : I64) (hx : Bounded b x) (hv : -b ≤ v.val ∧ v.val ≤ b) :
    Bounded b (x.set i v) := by
  intro z hz
  have hz' : z = v ∨ z ∈ x.val := by
    have hmem : z ∈ x.val.set i.val v := by simpa [Array.set_val_eq] using hz
    exact (List.mem_or_eq_of_mem_set hmem).symm
  rcases hz' with rfl | hz'
  · exact hv
  · exact hx z hz'

/-- Total correctness of both real projection loops. -/
theorem project_spec (x : Array I64 128#usize)
    (w : Array (Array I8 32#usize) 128#usize) (bx bw : Int)
    (hbx : 0 ≤ bx) (hbw : 0 ≤ bw) (hx : Bounded bx x) (hw : MatrixBound bw w)
    (henv : 128 * bx * bw ≤ Envelope.value) :
    general_engine.project x w ⦃ r =>
      ints r = GeneralModel.project (ints x) (w.val.map (fun row => row.val.map (·.val))) ∧
      Bounded (128 * bx * bw) r ⦄ := by
  have hb : 0 ≤ 128 * bx * bw := by positivity
  have hrows : ∀ row ∈ w.val.map (fun row => row.val.map (·.val)), row.length = 32 := by
    simp only [List.mem_map]
    rintro row ⟨r, _, rfl⟩
    simp
  unfold general_engine.project general_engine.project_loop0
  apply loop.spec_decr_nat
    (measure := fun (s : Array I64 32#usize × Usize) => 32 - s.2.val)
    (inv := fun (s : Array I64 32#usize × Usize) =>
      s.2.val ≤ 32 ∧ Bounded (128 * bx * bw) s.1 ∧
      ∀ (j : Nat) (hj : j < 32), j < s.2.val →
        (ints s.1)[j]'(by simpa [ints] using hj) =
          GeneralModel.dot (ints x) (project_column w j))
  · rintro ⟨out, i⟩ ⟨hi, hout, heq⟩
    unfold general_engine.project_loop0.body
    dsimp only at hi hout heq ⊢
    simp only [general_engine.D_HEAD]
    split
    · have hi32 : i.val < 32 := by scalar_tac
      step with project_inner_spec x w i bx bw hi32 hbx hbw hx hw henv as ⟨acc, hacc, hacclo, hacchi⟩
      step as ⟨out1, hout1⟩
      step as ⟨i1, hi1⟩
      simp only [hi1]
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [hout1]
        exact project_bounded_set _ _ _ _ hout ⟨hacclo, hacchi⟩
      · intro j hj32 hj
        by_cases hji : j = i.val
        · subst j
          simpa [ints, hout1] using hacc
        · have hjold : j < i.val := by omega
          simpa [ints, hout1, Ne.symm hji] using heq j hj32 hjold
    · have hi32 : i.val = 32 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, hout⟩
      apply List.ext_getElem
      · simp [ints, GeneralModel.project, project_lincomb_length _ _ _ hrows]
      · intro j hj hj'
        rw [heq j (by simpa [ints] using hj) (by simpa [ints, hi32] using hj)]
        simpa [GeneralModel.project, project_column, List.map_map, Function.comp_def] using
          (project_lincomb_get 32 (ints x) _ hrows j (by simpa [ints] using hj)).symm
  · simp only
    refine ⟨by scalar_tac, ?_, ?_⟩
    · intro v hv
      have : v = 0#i64 := by simpa using hv
      subst v
      scalar_tac
    · intro j hj32 hj
      simp at hj

theorem project_dot_bound (xs ys : List Int) (bx bw : Int)
    (hbx : 0 ≤ bx) (hbw : 0 ≤ bw)
    (hx : ∀ x ∈ xs, -bx ≤ x ∧ x ≤ bx) (hy : ∀ y ∈ ys, -bw ≤ y ∧ y ≤ bw) :
    -(xs.length : Int) * (bx * bw) ≤ GeneralModel.dot xs ys ∧
    GeneralModel.dot xs ys ≤ (xs.length : Int) * (bx * bw) := by
  have hb := mul_nonneg hbx hbw
  induction xs generalizing ys with
  | nil => simp [GeneralModel.dot]
  | cons x xs ih =>
    cases ys with
    | nil =>
      simp only [GeneralModel.dot]
      change -((x :: xs).length : Int) * (bx * bw) ≤ 0 ∧
        0 ≤ ((x :: xs).length : Int) * (bx * bw)
      have hh : 0 ≤ ((x :: xs).length : Int) * (bx * bw) := mul_nonneg (by omega) hb
      constructor <;> nlinarith only [hh]
    | cons y ys =>
      have hp := project_mul_bound x y bx bw hbx hbw (hx x (by simp)) (hy y (by simp))
      have hs := ih ys (by intro z hz; exact hx z (by simp [hz]))
        (by intro z hz; exact hy z (by simp [hz]))
      simp only [GeneralModel.dot, List.length_cons, Nat.cast_add, Nat.cast_one, Int.add_def, Int.mul_def]
      constructor <;> nlinarith only [hp.1, hp.2, hs.1, hs.2]

/-- Total correctness of embedding, using precisely the accepted token and position bounds. -/
theorem embed_spec (W : general_engine.Weights) (hW : LoadBounds W) (t p : Usize)
    (ht : t.val < 256) (hp : p.val < 32) :
    general_engine.embed W t p ⦃ r =>
      ints r = GeneralModel.embed (toGeneralModel W) t.val p.val ∧
      Bounded Envelope.embedding r ⦄ := by
  let tr := W.tok.val[t.val]'(by simpa using ht)
  let pr := W.pos.val[p.val]'(by simpa using hp)
  let target := GeneralModel.addV (tr.val.map (·.val)) (pr.val.map (·.val))
  have hlen : target.length = 128 := by
    dsimp [target]
    rw [project_addV_length _ _ (by simp)]
    simp
  have htarget : GeneralModel.embed (toGeneralModel W) t.val p.val = target := by
    unfold GeneralModel.embed toGeneralModel
    rw [project_nth_eq _ _ _ (by simpa using ht), project_nth_eq _ _ _ (by simpa using hp)]
    simp only [List.getElem_map]
    rfl
  unfold general_engine.embed general_engine.embed_loop
  apply loop.spec_decr_nat
    (measure := fun (s : Array I64 128#usize × Usize) => 128 - s.2.val)
    (inv := fun (s : Array I64 128#usize × Usize) =>
      s.2.val ≤ 128 ∧ Bounded Envelope.embedding s.1 ∧
      ∀ (j : Nat) (hj : j < 128), j < s.2.val →
        (ints s.1)[j]'(by simpa [ints] using hj) = target[j]'(by omega))
  · rintro ⟨out, k⟩ ⟨hk, hout, heq⟩
    unfold general_engine.embed_loop.body
    dsimp only at hk hout heq ⊢
    simp only [general_engine.D_MODEL]
    split
    · have hk128 : k.val < 128 := by scalar_tac
      step as ⟨rowt, hrowt⟩
      step as ⟨tv, htv⟩
      have htvb := hW.tok rowt (by simp [hrowt]) tv (by simp [htv])
      step as ⟨tv64, htv64⟩
      step as ⟨rowp, hrowp⟩
      step as ⟨pv, hpv⟩
      have hpvb := hW.pos rowp (by simp [hrowp]) pv (by simp [hpv])
      step as ⟨pv64, hpv64⟩
      step as ⟨v, hv⟩
      step as ⟨out1, hout1⟩
      step as ⟨k1, hk1⟩
      have hvsum : v.val = tv.val + pv.val := by scalar_tac
      have hvtarget : v.val = target[k.val]'(by omega) := by
        dsimp [target]
        rw [project_addV_get _ _ (by simp) k.val (by simpa using hk128)]
        simpa [tr, pr, hrowt, hrowp, htv, hpv] using hvsum
      simp only [hk1]
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [hout1]
        apply project_bounded_set _ _ _ _ hout
        change -127 ≤ v.val ∧ v.val ≤ 127
        omega
      · intro j hj128 hj
        by_cases hjk : j = k.val
        · subst j
          simpa [ints, hout1] using hvtarget
        · have hjold : j < k.val := by omega
          simpa [ints, hout1, Ne.symm hjk] using heq j hj128 hjold
    · have hk128 : k.val = 128 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, hout⟩
      rw [htarget]
      apply List.ext_getElem
      · simpa [ints] using hlen.symm
      · intro j hj hj'
        exact heq j (by simpa [ints] using hj) (by simpa [ints, hk128] using hj)
  · simp only
    refine ⟨by scalar_tac, ?_, ?_⟩
    · intro v hv
      have : v = 0#i64 := by simpa using hv
      subst v
      change -127 ≤ (0#i64).val ∧ (0#i64).val ≤ 127
      scalar_tac
    · intro j hj128 hj
      simp at hj

theorem embed_eq (W : general_engine.Weights) (hW : LoadBounds W) (t p : Usize)
    (ht : t.val < 256) (hp : p.val < 32) :
    ∃ r, general_engine.embed W t p = ok r ∧
      ints r = GeneralModel.embed (toGeneralModel W) t.val p.val ∧
      Bounded Envelope.embedding r := by
  have h := embed_spec W hW t p ht hp
  cases heq : general_engine.embed W t p with
  | ret r => exact ⟨r, rfl, by simpa [heq] using h⟩
  | vis e k => simp [heq] at h
  | div => simp [heq] at h

/-- Total correctness of the row read: the row is copied and keeps its bound. -/
theorem row_at_spec (x : Array (Array I64 128#usize) 32#usize) (p : Usize)
    (hp : p.val < 32) (b : Int) (hb0 : 0 ≤ b)
    (hb : Bounded b (x.val[p.val]'(by simpa using hp))) :
    general_engine.row_at x p ⦃ r =>
      ints r = GeneralModel.rowAt (ints2 x) p.val ∧ Bounded b r ⦄ := by
  let target : List Int := (x.val[p.val]'(by simpa using hp)).val.map (·.val)
  have hlen : target.length = 128 := by simp [target]
  have htarget : GeneralModel.rowAt (ints2 x) p.val = target := by
    simp only [GeneralModel.rowAt, ints2]
    rw [project_nth_eq _ _ _ (by simpa [ints2] using hp)]
    simp [target, ints]
  unfold general_engine.row_at general_engine.row_at_loop
  apply loop.spec_decr_nat
    (measure := fun (s : Array I64 128#usize × Usize) => 128 - s.2.val)
    (inv := fun (s : Array I64 128#usize × Usize) =>
      s.2.val ≤ 128 ∧ Bounded b s.1 ∧
      ∀ (j : Nat) (hj : j < 128), j < s.2.val →
        (ints s.1)[j]'(by simpa [ints] using hj) = target[j]'(by omega))
  · rintro ⟨out, k⟩ ⟨hk, hout, heq⟩
    unfold general_engine.row_at_loop.body
    dsimp only at hk hout heq ⊢
    simp only [general_engine.D_MODEL]
    split
    · have hk128 : k.val < 128 := by scalar_tac
      step as ⟨rowx, hrowx⟩
      step as ⟨xv, hxv⟩
      have hxb := hb xv (by simp [hxv, hrowx])
      step as ⟨out1, hout1⟩
      step as ⟨k1, hk1⟩
      have hvtarget : xv.val = target[k.val]'(by omega) := by
        simp [target, hrowx, hxv]
      simp only [hk1]
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [hout1]
        exact project_bounded_set _ _ _ _ hout hxb
      · intro j hj128 hj
        by_cases hjk : j = k.val
        · subst j
          simpa [ints, hout1] using hvtarget
        · have hjold : j < k.val := by omega
          simpa [ints, hout1, Ne.symm hjk] using heq j hj128 hjold
    · have hk128 : k.val = 128 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, hout⟩
      rw [htarget]
      apply List.ext_getElem
      · simpa [ints] using hlen.symm
      · intro j hj hj'
        exact heq j (by simpa [ints] using hj) (by simpa [ints, hk128] using hj)
  · simp only
    refine ⟨by scalar_tac, ?_, ?_⟩
    · intro v hv
      have : v = 0#i64 := by simpa using hv
      subst v
      have hz : (0#i64).val = 0 := by simp
      omega
    · intro j hj128 hj
      simp at hj

/-- The row read as an existential stage: exact value plus the propagated bound. -/
theorem row_at_eq (x : Array (Array I64 128#usize) 32#usize) (p : Usize)
    (hp : p.val < 32) (b : Int) (hb0 : 0 ≤ b)
    (hb : Bounded b (x.val[p.val]'(by simpa using hp))) :
    ∃ r, general_engine.row_at x p = ok r ∧
      ints r = GeneralModel.rowAt (ints2 x) p.val ∧ Bounded b r := by
  have h := row_at_spec x p hp b hb0 hb
  cases heq : general_engine.row_at x p with
  | ret r => exact ⟨r, rfl, by simpa [heq] using h⟩
  | vis e k => simp [heq] at h
  | div => simp [heq] at h

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
    GeneralModel.nth 0 (a.val.map (·.val)) i.val = (a.val[i.val]'(by simpa using hi)).val := by
  rw [project_nth_eq _ _ _ (by simpa using hi), List.getElem_map]

theorem exp_spec (W : general_engine.Weights) (hW : LoadBounds W) (d : I64) (_hd : 0 ≤ d.val) :
    general_engine.exp_fix W d ⦃ r => r.val = GeneralModel.expFix (toGeneralModel W) d.val ∧
      0 ≤ r.val ∧ r.val ≤ 1073741824 ⦄ := by
  unfold general_engine.exp_fix
  simp only [general_engine.EXP_FRAC_BITS]
  split
  · have hz : d.val ≤ 0 := by scalar_tac
    have hone : general_engine.EXP_ONE = ok 1073741824#i64 := by
      unfold general_engine.EXP_ONE; rfl
    simp [hone, GeneralModel.expFix, hz, GeneralModel.EXP_ONE]
  · have hpos : ¬d.val ≤ 0 := by scalar_tac
    step as ⟨u, hu, _⟩
    step as ⟨n, hn, _⟩
    change u.val = Int.shiftRight d.val 8 at hu
    change n.val = Int.shiftRight u.val 24 at hn
    have hu0 : 0 ≤ u.val := by rw [hu]; change 0 ≤ d.val >>> 8; rw [Int.shiftRight_eq_div_pow]; omega
    have hn0 : 0 ≤ n.val := by rw [hn]; change 0 ≤ u.val >>> 24; rw [Int.shiftRight_eq_div_pow]; omega
    simp only [general_engine.EXP_N_LEN]
    split
    · have hn32 : 32 ≤ n.val := by scalar_tac
      simp [GeneralModel.expFix, hpos, ←hu, ←hn, hn32]
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
      simp only [GeneralModel.expFix, hpos, ite_false, ←hu, ←hn,
        show ¬32 ≤ n.val by omega, toGeneralModel]
      rw [←hb2, ←hb1, ←hb0, ←hni', ←hj2', ←hj1', ←hj0']
      rw [exp_table_nth W.exp_n ni (by scalar_tac),
        exp_table_nth W.exp_2 j2 (by scalar_tac),
        exp_table_nth W.exp_1 j1 (by scalar_tac),
        exp_table_nth W.exp_0 j0 (by scalar_tac)]
      simp only [←he, ←ht2, ←ht1, ←ht0]
      rw [hr, hp0v, he2, hp1v, he1, hp2v]
      rfl

end LcnExec.GeneralEngine
