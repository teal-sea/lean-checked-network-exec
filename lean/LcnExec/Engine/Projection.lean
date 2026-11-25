import LcnExec.Engine.Stages

open Aeneas Aeneas.Std Result ControlFlow
namespace LcnExec.Engine

theorem project_nth_eq {α : Type} (d : α) (xs : List α) (i : Nat) (h : i < xs.length) :
    TransformerInt.nth d xs i = xs[i] := by
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
  w.val.map (fun row => TransformerInt.nth 0 (row.val.map (·.val)) i)

/-- Total correctness and the prefix envelope of the translated contraction loop. -/
theorem project_inner_spec (x : Array I64 128#usize)
    (w : Array (Array I8 32#usize) 128#usize) (i : Usize)
    (bx bw : Int) (hi : i.val < 32) (hbx : 0 ≤ bx) (hbw : 0 ≤ bw)
    (hx : Bounded bx x) (hw : MatrixBound bw w)
    (henv : 128 * bx * bw ≤ Envelope.value) :
    engine.project_loop0_loop0 x w i 0#i64 0#usize ⦃ r =>
      r.val = TransformerInt.dot (ints x) (project_column w i.val) ∧
      -(128 * bx * bw) ≤ r.val ∧ r.val ≤ 128 * bx * bw ⦄ := by
  have hb : 0 ≤ bx * bw := mul_nonneg hbx hbw
  change 128 * bx * bw ≤ 1723136 at henv
  have hprod : bx * bw ≤ 1723136 := by nlinarith
  unfold engine.project_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (s : I64 × Usize) => 128 - s.2.val)
    (inv := fun (s : I64 × Usize) =>
      s.2.val ≤ 128 ∧
      s.1.val + TransformerInt.dot ((ints x).drop s.2.val)
        ((project_column w i.val).drop s.2.val) =
          TransformerInt.dot (ints x) (project_column w i.val) ∧
      -(s.2.val : Int) * (bx * bw) ≤ s.1.val ∧
      s.1.val ≤ (s.2.val : Int) * (bx * bw))
  · rintro ⟨acc, k⟩ ⟨hk, hacc, hlo, hhi⟩
    unfold engine.project_loop0_loop0.body
    dsimp only at hk hacc hlo hhi ⊢
    simp only [engine.D_MODEL]
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
      simpa [hk128, ints, project_column, TransformerInt.dot, mul_assoc] using
        And.intro hacc (And.intro hlo hhi)
  · simp

theorem project_addV_length (xs ys : List Int) (h : xs.length = ys.length) :
    (TransformerInt.addV xs ys).length = xs.length := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys => simpa [TransformerInt.addV] using ih ys (by simpa using h)

theorem project_addV_get (xs ys : List Int) (h : xs.length = ys.length)
    (i : Nat) (hi : i < xs.length) :
    (TransformerInt.addV xs ys)[i]'(by rw [project_addV_length xs ys h]; exact hi) =
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
    TransformerInt.scale c xs = xs.map (fun x => c * x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [TransformerInt.scale, ih]

theorem project_lincomb_length (n : Nat) (xs : List Int) (ws : List (List Int))
    (hw : ∀ row ∈ ws, row.length = n) :
    (TransformerInt.lincomb n xs ws).length = n := by
  induction xs generalizing ws with
  | nil => simp [TransformerInt.lincomb]
  | cons x xs ih =>
    cases ws with
    | nil => simp [TransformerInt.lincomb]
    | cons row ws =>
      have hr := hw row (by simp)
      have hs := ih ws (by intro r h; exact hw r (by simp [h]))
      simp only [TransformerInt.lincomb]
      rw [project_addV_length _ _ (by simpa [project_scale_eq] using hr.trans hs.symm)]
      simpa [project_scale_eq] using hr

theorem project_lincomb_get (n : Nat) (xs : List Int) (ws : List (List Int))
    (hw : ∀ row ∈ ws, row.length = n) (i : Nat) (hi : i < n) :
    (TransformerInt.lincomb n xs ws)[i]'(by rw [project_lincomb_length n xs ws hw]; exact hi) =
      TransformerInt.dot xs (ws.map (fun row => TransformerInt.nth 0 row i)) := by
  induction xs generalizing ws with
  | nil => simp [TransformerInt.lincomb, TransformerInt.dot]
  | cons x xs ih =>
    cases ws with
    | nil => simp [TransformerInt.lincomb, TransformerInt.dot]
    | cons row ws =>
      have hr := hw row (by simp)
      have hws : ∀ r ∈ ws, r.length = n := by intro r h; exact hw r (by simp [h])
      have hs := project_lincomb_length n xs ws hws
      simp only [TransformerInt.lincomb]
      rw [project_addV_get _ _ (by simp [project_scale_eq, hr, hs]) i (by simp [project_scale_eq, hr, hi])]
      simp [project_scale_eq, project_nth_eq, hr, hi, ih ws hws, TransformerInt.dot]

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
    engine.project x w ⦃ r =>
      ints r = TransformerInt.project (ints x) (w.val.map (fun row => row.val.map (·.val))) ∧
      Bounded (128 * bx * bw) r ⦄ := by
  have hb : 0 ≤ 128 * bx * bw := by positivity
  have hrows : ∀ row ∈ w.val.map (fun row => row.val.map (·.val)), row.length = 32 := by
    simp only [List.mem_map]
    rintro row ⟨r, _, rfl⟩
    simp
  unfold engine.project engine.project_loop0
  apply loop.spec_decr_nat
    (measure := fun (s : Array I64 32#usize × Usize) => 32 - s.2.val)
    (inv := fun (s : Array I64 32#usize × Usize) =>
      s.2.val ≤ 32 ∧ Bounded (128 * bx * bw) s.1 ∧
      ∀ (j : Nat) (hj : j < 32), j < s.2.val →
        (ints s.1)[j]'(by simpa [ints] using hj) =
          TransformerInt.dot (ints x) (project_column w j))
  · rintro ⟨out, i⟩ ⟨hi, hout, heq⟩
    unfold engine.project_loop0.body
    dsimp only at hi hout heq ⊢
    simp only [engine.D_HEAD]
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
      · simp [ints, TransformerInt.project, project_lincomb_length _ _ _ hrows]
      · intro j hj hj'
        rw [heq j (by simpa [ints] using hj) (by simpa [ints, hi32] using hj)]
        simpa [TransformerInt.project, project_column, List.map_map, Function.comp_def] using
          (project_lincomb_get 32 (ints x) _ hrows j (by simpa [ints] using hj)).symm
  · simp only
    refine ⟨by scalar_tac, ?_, ?_⟩
    · intro v hv
      have : v = 0#i64 := by simpa using hv
      subst v
      scalar_tac
    · intro j hj32 hj
      simp at hj

theorem project_eq : ProjectStage := by
  intro x w bx bw hbx hbw hx hw henv
  have h := project_spec x w bx bw hbx hbw hx hw henv
  cases heq : engine.project x w with
  | ret r => exact ⟨r, rfl, by simpa [heq] using h⟩
  | vis e k => simp [heq] at h
  | div => simp [heq] at h

/-- Total correctness of embedding, using precisely the accepted token and position bounds. -/
theorem embed_spec (W : engine.Weights) (hW : LoadBounds W) (t p : Usize)
    (ht : t.val < 114) (hp : p.val < 3) :
    engine.embed W t p ⦃ r =>
      ints r = TransformerInt.embed (toModel W) t.val p.val ∧
      Bounded Envelope.embedding r ⦄ := by
  let tr := W.tok.val[t.val]'(by simpa using ht)
  let pr := W.pos.val[p.val]'(by simpa using hp)
  let target := TransformerInt.addV (tr.val.map (·.val)) (pr.val.map (·.val))
  have hlen : target.length = 128 := by
    dsimp [target]
    rw [project_addV_length _ _ (by simp)]
    simp
  have htarget : TransformerInt.embed (toModel W) t.val p.val = target := by
    unfold TransformerInt.embed toModel
    rw [project_nth_eq _ _ _ (by simpa using ht), project_nth_eq _ _ _ (by simpa using hp)]
    simp only [List.getElem_map]
    rfl
  unfold engine.embed engine.embed_loop
  apply loop.spec_decr_nat
    (measure := fun (s : Array I64 128#usize × Usize) => 128 - s.2.val)
    (inv := fun (s : Array I64 128#usize × Usize) =>
      s.2.val ≤ 128 ∧ Bounded Envelope.embedding s.1 ∧
      ∀ (j : Nat) (hj : j < 128), j < s.2.val →
        (ints s.1)[j]'(by simpa [ints] using hj) = target[j]'(by omega))
  · rintro ⟨out, k⟩ ⟨hk, hout, heq⟩
    unfold engine.embed_loop.body
    dsimp only at hk hout heq ⊢
    simp only [engine.D_MODEL]
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

theorem embed_eq : EmbedStage := by
  intro W hW t p ht hp
  have h := embed_spec W hW t p ht hp
  cases heq : engine.embed W t p with
  | ret r => exact ⟨r, rfl, by simpa [heq] using h⟩
  | vis e k => simp [heq] at h
  | div => simp [heq] at h

theorem project_dot_bound (xs ys : List Int) (bx bw : Int)
    (hbx : 0 ≤ bx) (hbw : 0 ≤ bw)
    (hx : ∀ x ∈ xs, -bx ≤ x ∧ x ≤ bx) (hy : ∀ y ∈ ys, -bw ≤ y ∧ y ≤ bw) :
    -(xs.length : Int) * (bx * bw) ≤ TransformerInt.dot xs ys ∧
    TransformerInt.dot xs ys ≤ (xs.length : Int) * (bx * bw) := by
  have hb := mul_nonneg hbx hbw
  induction xs generalizing ys with
  | nil => simp [TransformerInt.dot]
  | cons x xs ih =>
    cases ys with
    | nil =>
      simp only [TransformerInt.dot]
      change -((x :: xs).length : Int) * (bx * bw) ≤ 0 ∧
        0 ≤ ((x :: xs).length : Int) * (bx * bw)
      have hh : 0 ≤ ((x :: xs).length : Int) * (bx * bw) := mul_nonneg (by omega) hb
      constructor <;> nlinarith only [hh]
    | cons y ys =>
      have hp := project_mul_bound x y bx bw hbx hbw (hx x (by simp)) (hy y (by simp))
      have hs := ih ys (by intro z hz; exact hx z (by simp [hz]))
        (by intro z hz; exact hy z (by simp [hz]))
      simp only [TransformerInt.dot, List.length_cons, Nat.cast_add, Nat.cast_one, Int.add_def, Int.mul_def]
      constructor <;> nlinarith only [hp.1, hp.2, hs.1, hs.2]

theorem scores_dot_spec (q k : Array I64 32#usize)
    (hq : Bounded Envelope.query q) (hk : Bounded Envelope.key k) :
    engine.dot q k ⦃ r => r.val = TransformerInt.dot (ints q) (ints k) ∧
      -Envelope.score ≤ r.val ∧ r.val ≤ Envelope.score ⦄ := by
  have hqs : Small q := by
    intro v hv
    have h := hq v hv
    change -81280 ≤ v.val ∧ v.val ≤ 81280 at h
    omega
  have hks : Small k := by
    intro v hv
    have h := hk v hv
    change -357632 ≤ v.val ∧ v.val ≤ 357632 at h
    omega
  have hb := project_dot_bound (ints q) (ints k) 81280 357632 (by omega) (by omega)
    (by simpa [ints, Bounded, Envelope.query] using hq)
    (by simpa [ints, Bounded, Envelope.key] using hk)
  have hd := dot_spec q k hqs hks
  cases heq : engine.dot q k with
  | ret r =>
    have hr : r.val = TransformerInt.dot (ints q) (ints k) := by simpa [heq] using hd
    simp only [WP.spec_ok]
    have hb' : -930186526720 ≤ TransformerInt.dot (ints q) (ints k) ∧
        TransformerInt.dot (ints q) (ints k) ≤ 930186526720 := by simpa [ints] using hb
    exact ⟨hr, by simpa [hr, Envelope.score] using hb'⟩
  | vis e k => simp [heq] at hd
  | div => simp [heq] at hd

/-- All three scores, with the loop's complete array invariant. -/
theorem scores_loop_spec
    (a : Array (Array (Array I8 32#usize) 128#usize) 4#usize)
    (h : Usize) (x : Array (Array I64 128#usize) 3#usize)
    (q : Array I64 32#usize) (ha : TensorBound 22 a) (hh : h.val < 4)
    (hx : streams x) (hq : Bounded Envelope.query q) :
    engine.head_scores_loop a h x q (Array.repeat 3#usize 0#i64) 0#usize ⦃ r =>
      Bounded Envelope.score r ∧
      ∀ (j : Nat) (hj : j < 3), (ints r)[j]'(by simpa [ints] using hj) =
        TransformerInt.dot (ints q)
          (TransformerInt.project (stream x j)
            ((a.val[h.val]'(by simpa using hh)).val.map (fun row => row.val.map (·.val)))) ⦄ := by
  let mat := a.val[h.val]'(by simpa using hh)
  let score := fun j => TransformerInt.dot (ints q)
    (TransformerInt.project (stream x j) (mat.val.map (fun row => row.val.map (·.val))))
  unfold engine.head_scores_loop
  apply loop.spec_decr_nat
    (measure := fun (s : Array I64 3#usize × Usize) => 3 - s.2.val)
    (inv := fun (s : Array I64 3#usize × Usize) =>
      s.2.val ≤ 3 ∧ Bounded Envelope.score s.1 ∧
      ∀ (j : Nat) (hj : j < 3), j < s.2.val →
        (ints s.1)[j]'(by simpa [ints] using hj) = score j)
  · rintro ⟨out, j⟩ ⟨hj, hout, heq⟩
    unfold engine.head_scores_loop.body
    dsimp only at hj hout heq ⊢
    simp only [engine.N_POS]
    split
    · have hj3 : j.val < 3 := by scalar_tac
      step as ⟨rowx, hrowx⟩
      step as ⟨w, hw⟩
      have hxrow := hx rowx (by simp [hrowx])
      have hwmat := ha w (by simp [hw])
      step with project_spec rowx w Envelope.embedding 22 (by decide) (by omega)
        hxrow hwmat (by decide) as ⟨key, hkey, hkeyb⟩
      have hkb : Bounded Envelope.key key := by simpa [Envelope.key, Envelope.embedding] using hkeyb
      step with scores_dot_spec q key hq hkb as ⟨v, hv, hvlo, hvhi⟩
      step as ⟨out1, hout1⟩
      step as ⟨j1, hj1⟩
      have hvscore : v.val = score j.val := by
        rw [hv, hkey]
        have hs : stream x j.val = ints rowx := by
          unfold stream
          rw [project_nth_eq _ _ _ (by simpa using hj3)]
          simp [ints, hrowx]
        simp [score, hs, mat, hw]
      simp only [hj1]
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [hout1]
        exact project_bounded_set _ _ _ _ hout ⟨hvlo, hvhi⟩
      · intro k hk3 hk
        by_cases hkj : k = j.val
        · subst k
          simpa [ints, hout1] using hvscore
        · have hkold : k < j.val := by omega
          simpa [ints, hout1, Ne.symm hkj] using heq k hk3 hkold
    · have hj3 : j.val = 3 := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨hout, fun k hk => heq k hk (by omega)⟩
  · simp only
    refine ⟨by scalar_tac, ?_, ?_⟩
    · intro v hv
      have : v = 0#i64 := by simpa using hv
      subst v
      change -930186526720 ≤ (0#i64).val ∧ (0#i64).val ≤ 930186526720
      scalar_tac
    · intro j hj3 hj
      simp at hj

theorem scores_spec (W : engine.Weights) (hW : LoadBounds W) (h : Usize)
    (x : Array (Array I64 128#usize) 3#usize) (hh : h.val < 4) (hx : streams x) :
    engine.head_scores W h x ⦃ r =>
      triple r = TransformerInt.headScores (toModel W) h.val (stream x 0) (stream x 1) (stream x 2) ∧
      Bounded Envelope.score r ⦄ := by
  unfold engine.head_scores
  step as ⟨rowx, hrowx⟩
  step as ⟨w, hw⟩
  have hxrow := hx rowx (by simp [hrowx])
  have hwmat := hW.wq w (by simp [hw])
  step with project_spec rowx w Envelope.embedding 5 (by decide) (by omega)
    hxrow hwmat (by decide) as ⟨q, hq, hqb⟩
  have hqb' : Bounded Envelope.query q := by simpa [Envelope.query, Envelope.embedding] using hqb
  step with scores_loop_spec W.wk h x q hW.wk hh hx hqb' as ⟨r, hrb, hr⟩
  have hstream2 : stream x 2 = ints rowx := by
    unfold stream
    rw [project_nth_eq _ _ _ (by simp)]
    simp [ints, hrowx]
  have hqmodel : ints q = TransformerInt.project (stream x 2)
      (TransformerInt.nth [] (toModel W).wq h.val) := by
    rw [hq, hstream2]
    simp [toModel, project_nth_eq, hh, hw]
  have hwkmodel : TransformerInt.nth [] (toModel W).wk h.val =
      (W.wk.val[h.val]'(by simpa using hh)).val.map (fun row => row.val.map (·.val)) := by
    simp [toModel, project_nth_eq, hh]
  refine ⟨?_, hrb⟩
  unfold triple TransformerInt.headScores TransformerInt.keyScore
  rw [project_nth_eq _ _ _ (by simp [ints]), project_nth_eq _ _ _ (by simp [ints]),
    project_nth_eq _ _ _ (by simp [ints])]
  rw [hr 0 (by omega), hr 1 (by omega), hr 2 (by omega), hqmodel, hwkmodel]

theorem scores_eq : ScoreStage := by
  intro W hW h x hh hx
  have hs := scores_spec W hW h x hh hx
  cases heq : engine.head_scores W h x with
  | ret r => exact ⟨r, rfl, by simpa [heq] using hs⟩
  | vis e k => simp [heq] at hs
  | div => simp [heq] at hs

#print axioms project_addV_length
#print axioms project_addV_get
#print axioms project_scale_eq
#print axioms project_lincomb_length
#print axioms project_lincomb_get
#print axioms scores_loop_spec
#print axioms scores_spec
#print axioms scores_eq
#print axioms project_dot_bound
#print axioms scores_dot_spec
#print axioms embed_spec
#print axioms embed_eq
#print axioms project_bounded_set
#print axioms project_spec
#print axioms project_eq
#print axioms project_nth_eq
#print axioms project_mul_bound
#print axioms project_inner_spec
end LcnExec.Engine
