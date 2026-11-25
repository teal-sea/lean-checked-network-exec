import LcnExec.Engine.Stages

open Aeneas Aeneas.Std Result ControlFlow
namespace LcnExec.Engine

/-- Total correctness and soundness of the translated byte-vector checker. -/
@[step]
theorem bounded_i8_spec {n : Usize} (xs : Array I8 n) (limit : I8)
    (hl : 0 ≤ limit.val) :
    engine.bounded_i8 xs limit ⦃ b => b = true →
      ∀ v ∈ xs.val, -limit.val ≤ v.val ∧ v.val ≤ limit.val ⦄ := by
  unfold engine.bounded_i8 engine.bounded_i8_loop
  apply loop.spec_decr_nat
    (measure := fun i => n.val - i.val)
    (inv := fun i => i.val ≤ n.val ∧
      ∀ j : Nat, j < i.val → -limit.val ≤ xs.val[j]!.val ∧ xs.val[j]!.val ≤ limit.val)
  · intro i
    rintro ⟨hi, hp⟩
    unfold engine.bounded_i8_loop.body
    split
    · rename_i hlt
      have hin : i.val < n.val := by scalar_tac
      step as ⟨v, hv⟩
      step as ⟨neg, hn⟩
      split
      · simp
      · rename_i hlo
        split
        · simp
        · rename_i hhi
          step as ⟨i1, hi1⟩
          simp only [hi1]
          refine ⟨by omega, ?_, by omega⟩
          intro j hj
          by_cases hj0 : j < i.val
          · exact hp j hj0
          · have he : j = i.val := by omega
            subst j
            simpa only [getElem!_pos xs.val i.val (by simpa using hin), hv] using (show -limit.val ≤ v.val ∧ v.val ≤ limit.val by scalar_tac)
    · simp only [WP.spec_ok]
      intro _ v hv
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
      have hlen : xs.val.length = n.val := by simp
      have hi' : i.val = n.val := by scalar_tac
      simpa only [getElem!_pos xs.val j hj] using hp j (by omega)
  · simp

/-- Total correctness and soundness of the translated 64-bit vector checker. -/
@[step]
theorem bounded_i64_spec {n : Usize} (xs : Array I64 n) (limit : I64)
    (hl : 0 ≤ limit.val) :
    engine.bounded_i64 xs limit ⦃ b => b = true →
      ∀ v ∈ xs.val, -limit.val ≤ v.val ∧ v.val ≤ limit.val ⦄ := by
  unfold engine.bounded_i64 engine.bounded_i64_loop
  apply loop.spec_decr_nat
    (measure := fun i => n.val - i.val)
    (inv := fun i => i.val ≤ n.val ∧
      ∀ j : Nat, j < i.val → -limit.val ≤ xs.val[j]!.val ∧ xs.val[j]!.val ≤ limit.val)
  · intro i
    rintro ⟨hi, hp⟩
    unfold engine.bounded_i64_loop.body
    split
    · rename_i hlt
      have hin : i.val < n.val := by scalar_tac
      step as ⟨v, hv⟩
      step as ⟨neg, hn⟩
      split
      · simp
      · rename_i hlo
        split
        · simp
        · rename_i hhi
          step as ⟨i1, hi1⟩
          simp only [hi1]
          refine ⟨by omega, ?_, by omega⟩
          intro j hj
          by_cases hj0 : j < i.val
          · exact hp j hj0
          · have he : j = i.val := by omega
            subst j
            simpa only [getElem!_pos xs.val i.val (by simpa using hin), hv] using (show -limit.val ≤ v.val ∧ v.val ≤ limit.val by scalar_tac)
    · simp only [WP.spec_ok]
      intro _ v hv
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
      have hlen : xs.val.length = n.val := by simp
      have hi' : i.val = n.val := by scalar_tac
      simpa only [getElem!_pos xs.val j hj] using hp j (by omega)
  · simp


/-- Total correctness and soundness of the translated exponential table checker. -/
@[step]
theorem table_spec {n : Usize} (xs : Array I64 n) :
    engine.table xs ⦃ b => b = true →
      ∀ v ∈ xs.val, 0 ≤ v.val ∧ v.val ≤ 1073741824 ⦄ := by
  unfold engine.table engine.table_loop
  apply loop.spec_decr_nat
    (measure := fun i => n.val - i.val)
    (inv := fun i => i.val ≤ n.val ∧
      ∀ j : Nat, j < i.val → 0 ≤ xs.val[j]!.val ∧ xs.val[j]!.val ≤ 1073741824)
  · intro i
    rintro ⟨hi, hp⟩
    unfold engine.table_loop.body
    split
    · rename_i hlt
      have hin : i.val < n.val := by scalar_tac
      step as ⟨v, hv⟩
      split
      · simp
      · rename_i hlo
        simp only [engine.EXP_ONE]
        step as ⟨expOne, hexpOne⟩
        have hcalc : ((1 : Int) <<< (30 : Nat)).bmod 18446744073709551616 = 1073741824 := by decide
        rw [I64.size_eq, hcalc] at hexpOne
        split
        · simp
        · rename_i hhi
          step as ⟨i1, hi1⟩
          simp only [hi1]
          refine ⟨by omega, ?_, by omega⟩
          intro j hj
          by_cases hj0 : j < i.val
          · exact hp j hj0
          · have he : j = i.val := by omega
            subst j
            simpa only [getElem!_pos xs.val i.val (by simpa using hin), hv] using (show 0 ≤ v.val ∧ v.val ≤ 1073741824 by scalar_tac)
    · simp only [WP.spec_ok]
      intro _ v hv
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
      have hlen : xs.val.length = n.val := by simp
      have hi' : i.val = n.val := by scalar_tac
      simpa only [getElem!_pos xs.val j hj] using hp j (by omega)
  · simp


#print axioms bounded_i8_spec
#print axioms bounded_i64_spec
#print axioms table_spec

/-- Extend an index-based invariant by the just-checked element. -/
theorem load_prefix_succ {α : Type} [Inhabited α] (P : α → Prop)
    (xs : List α) (i : Nat) (hp : ∀ j < i, P xs[j]!) (hv : P xs[i]!) :
    ∀ j < i + 1, P xs[j]! := by
  intro j hj
  by_cases h : j < i
  · exact hp j h
  · have : j = i := by omega
    simpa [this] using hv

/-- Convert the completed loop invariant to a membership specification. -/
theorem load_prefix_all {α : Type} [Inhabited α] (P : α → Prop)
    (xs : List α) (hp : ∀ j < xs.length, P xs[j]!) : ∀ v ∈ xs, P v := by
  intro v hv
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
  simpa only [getElem!_pos xs j hj] using hp j hj

@[step]
theorem load_tok_spec (w : engine.Weights) (valid : Bool) :
    engine.load_check_loop0 w valid 0#usize ⦃ r =>
      r.1 = w ∧ (r.2 = true → valid = true ∧ MatrixBound 68 w.tok) ⦄ := by
  unfold engine.load_check_loop0
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 114 - s.2.val)
    (inv := fun s : Bool × Usize => s.2.val ≤ 114 ∧
      (s.1 = true → valid = true ∧
        ∀ j < s.2.val, ∀ v ∈ w.tok.val[j]!.val, -68 ≤ v.val ∧ v.val ≤ 68))
  · rintro ⟨b, i⟩ ⟨hi, hp⟩
    unfold engine.load_check_loop0.body
    dsimp only at hi hp ⊢
    split
    · rename_i hlt
      have hin : i.val < 114 := by scalar_tac
      step as ⟨row, hrow⟩
      step as ⟨checked, hc⟩
      split
      · rename_i hchecked
        step as ⟨i1, hi1⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro hb
        obtain ⟨hv, hpre⟩ := hp hb
        refine ⟨hv, ?_⟩
        rw [hi1]
        apply load_prefix_succ (fun row : Array I8 128#usize =>
          ∀ v ∈ row.val, -68 ≤ v.val ∧ v.val ≤ 68) w.tok.val i.val hpre
        simpa only [getElem!_pos w.tok.val i.val (by simpa using hin), ← hrow] using hc hchecked
      · step as ⟨i1, hi1⟩
        exact ⟨by scalar_tac, by simp, by scalar_tac⟩
    · simp only [WP.spec_ok]
      refine ⟨trivial, ?_⟩
      intro hb
      obtain ⟨hv, hpre⟩ := hp hb
      refine ⟨hv, ?_⟩
      apply load_prefix_all
      have hieq : i.val = 114 := by scalar_tac
      simpa [hieq] using hpre
  · simp

@[step]
theorem load_pos_spec (w : engine.Weights) (valid : Bool) :
    engine.load_check_loop1 w valid 0#usize ⦃ r =>
      r.1 = w ∧ (r.2.1 = true → valid = true ∧ MatrixBound 59 w.pos) ⦄ := by
  unfold engine.load_check_loop1
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 3 - s.2.val)
    (inv := fun s : Bool × Usize => s.2.val ≤ 3 ∧
      (s.1 = true → valid = true ∧
        ∀ j < s.2.val, ∀ v ∈ w.pos.val[j]!.val, -59 ≤ v.val ∧ v.val ≤ 59))
  · rintro ⟨b, i⟩ ⟨hi, hp⟩
    unfold engine.load_check_loop1.body
    dsimp only at hi hp ⊢
    split
    · rename_i hlt
      have hin : i.val < 3 := by scalar_tac
      step as ⟨row, hrow⟩
      step as ⟨checked, hc⟩
      split
      · rename_i hchecked
        step as ⟨i1, hi1⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro hb
        obtain ⟨hv, hpre⟩ := hp hb
        refine ⟨hv, ?_⟩
        rw [hi1]
        apply load_prefix_succ (fun row : Array I8 128#usize =>
          ∀ v ∈ row.val, -59 ≤ v.val ∧ v.val ≤ 59) w.pos.val i.val hpre
        simpa only [getElem!_pos w.pos.val i.val (by simpa using hin), ← hrow] using hc hchecked
      · step as ⟨i1, hi1⟩
        exact ⟨by scalar_tac, by simp, by scalar_tac⟩
    · simp only [WP.spec_ok]
      refine ⟨trivial, ?_⟩
      intro hb
      obtain ⟨hv, hpre⟩ := hp hb
      refine ⟨hv, ?_⟩
      apply load_prefix_all
      have hieq : i.val = 3 := by scalar_tac
      simpa [hieq] using hpre
  · simp

@[step]
theorem load_wout_spec (w : engine.Weights) (valid : Bool) :
    engine.load_check_loop4 w valid 0#usize ⦃ r =>
      r.1 = w ∧ (r.2 = true → valid = true ∧ MatrixBound 74 w.wout) ⦄ := by
  unfold engine.load_check_loop4
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 512 - s.2.val)
    (inv := fun s : Bool × Usize => s.2.val ≤ 512 ∧
      (s.1 = true → valid = true ∧
        ∀ j < s.2.val, ∀ v ∈ w.wout.val[j]!.val, -74 ≤ v.val ∧ v.val ≤ 74))
  · rintro ⟨b, i⟩ ⟨hi, hp⟩
    unfold engine.load_check_loop4.body
    dsimp only at hi hp ⊢
    split
    · rename_i hlt
      have hin : i.val < 512 := by scalar_tac
      step as ⟨row, hrow⟩
      step as ⟨checked, hc⟩
      split
      · rename_i hchecked
        step as ⟨i1, hi1⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro hb
        obtain ⟨hv, hpre⟩ := hp hb
        refine ⟨hv, ?_⟩
        rw [hi1]
        apply load_prefix_succ (fun row : Array I8 128#usize =>
          ∀ v ∈ row.val, -74 ≤ v.val ∧ v.val ≤ 74) w.wout.val i.val hpre
        simpa only [getElem!_pos w.wout.val i.val (by simpa using hin), ← hrow] using hc hchecked
      · step as ⟨i1, hi1⟩
        exact ⟨by scalar_tac, by simp, by scalar_tac⟩
    · simp only [WP.spec_ok]
      refine ⟨trivial, ?_⟩
      intro hb
      obtain ⟨hv, hpre⟩ := hp hb
      refine ⟨hv, ?_⟩
      apply load_prefix_all
      have hieq : i.val = 512 := by scalar_tac
      simpa [hieq] using hpre
  · simp

@[step]
theorem load_wo_spec (w : engine.Weights) (valid : Bool) (h : Usize) (hh : h.val < 4) :
    engine.load_check_loop2_loop1 w valid 0#usize h ⦃ r =>
      r.1 = w ∧ (r.2.1 = true → valid = true ∧ MatrixBound 93 (w.wo.val[h.val]!)) ⦄ := by
  unfold engine.load_check_loop2_loop1
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 32 - s.2.val)
    (inv := fun s : Bool × Usize => s.2.val ≤ 32 ∧
      (s.1 = true → valid = true ∧
        ∀ j < s.2.val, ∀ v ∈ (w.wo.val[h.val]!).val[j]!.val, -93 ≤ v.val ∧ v.val ≤ 93))
  · rintro ⟨b, i⟩ ⟨hi, hp⟩
    unfold engine.load_check_loop2_loop1.body
    dsimp only at hi hp ⊢
    split
    · rename_i hlt
      have hin : i.val < 32 := by scalar_tac
      step as ⟨mat, hmat⟩
      step as ⟨row, hrow⟩
      have hmat! : w.wo.val[h.val]! = mat := by
        simpa only [getElem!_pos w.wo.val h.val (by simpa using hh)] using hmat.symm

      step as ⟨checked, hc⟩
      split
      · rename_i hchecked
        step as ⟨i1, hi1⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro hb
        obtain ⟨hv, hpre⟩ := hp hb
        refine ⟨hv, ?_⟩
        rw [hi1]
        apply load_prefix_succ (fun row : Array I8 128#usize =>
          ∀ v ∈ row.val, -93 ≤ v.val ∧ v.val ≤ 93) (w.wo.val[h.val]!).val i.val hpre
        simpa only [hmat!, getElem!_pos mat.val i.val (by simpa using hin), ← hrow] using hc hchecked
      · step as ⟨i1, hi1⟩
        exact ⟨by scalar_tac, by simp, by scalar_tac⟩
    · simp only [WP.spec_ok]
      refine ⟨trivial, ?_⟩
      intro hb
      obtain ⟨hv, hpre⟩ := hp hb
      refine ⟨hv, ?_⟩
      apply load_prefix_all
      have hieq : i.val = 32 := by scalar_tac
      simpa [hieq] using hpre
  · simp


#print axioms load_pos_spec
#print axioms load_wout_spec
#print axioms load_wo_spec
#print axioms load_prefix_succ
#print axioms load_prefix_all
#print axioms load_tok_spec

/-- Bounds checked for one Q/K/V input coordinate. -/
def QkvRow (w : engine.Weights) (h i : Nat) : Prop :=
  (∀ v ∈ w.wq.val[h]!.val[i]!.val, -5 ≤ v.val ∧ v.val ≤ 5) ∧
  (∀ v ∈ w.wk.val[h]!.val[i]!.val, -22 ≤ v.val ∧ v.val ≤ 22) ∧
  (∀ v ∈ w.wv.val[h]!.val[i]!.val, -106 ≤ v.val ∧ v.val ≤ 106)

@[step]
theorem load_qkv_spec (w : engine.Weights) (valid : Bool) (h : Usize) (hh : h.val < 4) :
    engine.load_check_loop2_loop0 w valid 0#usize h ⦃ r => r.1 = w ∧
      (r.2 = true → valid = true ∧
        MatrixBound 5 w.wq.val[h.val]! ∧ MatrixBound 22 w.wk.val[h.val]! ∧
        MatrixBound 106 w.wv.val[h.val]!) ⦄ := by
  unfold engine.load_check_loop2_loop0
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 128 - s.2.val)
    (inv := fun s : Bool × Usize => s.2.val ≤ 128 ∧
      (s.1 = true → valid = true ∧ ∀ j < s.2.val, QkvRow w h.val j))
  · rintro ⟨b, i⟩ ⟨hi, hp⟩
    unfold engine.load_check_loop2_loop0.body
    dsimp only at hi hp ⊢
    split
    · rename_i hlt
      have hin : i.val < 128 := by scalar_tac
      step as ⟨qm, hqm⟩
      step as ⟨qr, hqr⟩
      step as ⟨qb, hqb⟩
      split
      · rename_i hqt
        step as ⟨km, hkm⟩
        step as ⟨kr, hkr⟩
        step as ⟨kb, hkb⟩
        split
        · rename_i hkt
          step as ⟨vm, hvm⟩
          step as ⟨vr, hvr⟩
          step as ⟨vb, hvb⟩
          split
          · rename_i hvt
            step as ⟨i1, hi1⟩
            refine ⟨by scalar_tac, ?_, by scalar_tac⟩
            intro hb
            obtain ⟨hv, hpre⟩ := hp hb
            refine ⟨hv, ?_⟩
            rw [hi1]
            intro j hj
            by_cases hj0 : j < i.val
            · exact hpre j hj0
            · have he : j = i.val := by omega
              subst j
              have hqm! : w.wq.val[h.val]! = qm := by
                simpa only [getElem!_pos w.wq.val h.val (by simpa using hh)] using hqm.symm
              have hkm! : w.wk.val[h.val]! = km := by
                simpa only [getElem!_pos w.wk.val h.val (by simpa using hh)] using hkm.symm
              have hvm! : w.wv.val[h.val]! = vm := by
                simpa only [getElem!_pos w.wv.val h.val (by simpa using hh)] using hvm.symm
              unfold QkvRow
              simp only [hqm!, hkm!, hvm!, getElem!_pos qm.val i.val (by simpa using hin),
                getElem!_pos km.val i.val (by simpa using hin),
                getElem!_pos vm.val i.val (by simpa using hin), ← hqr, ← hkr, ← hvr]
              exact ⟨hqb hqt, hkb hkt, hvb hvt⟩
          · step as ⟨i1, hi1⟩
            exact ⟨by scalar_tac, by simp, by scalar_tac⟩
        · step as ⟨i1, hi1⟩
          exact ⟨by scalar_tac, by simp, by scalar_tac⟩
      · step as ⟨i1, hi1⟩
        exact ⟨by scalar_tac, by simp, by scalar_tac⟩
    · simp only [WP.spec_ok]
      refine ⟨trivial, ?_⟩
      intro hb
      obtain ⟨hv, hpre⟩ := hp hb
      have hieq : i.val = 128 := by scalar_tac
      refine ⟨hv, ?_, ?_, ?_⟩
      · apply load_prefix_all
        intro j hj
        exact (hpre j (by simpa [hieq] using hj)).1
      · apply load_prefix_all
        intro j hj
        exact (hpre j (by simpa [hieq] using hj)).2.1
      · apply load_prefix_all
        intro j hj
        exact (hpre j (by simpa [hieq] using hj)).2.2
  · simp

#print axioms load_qkv_spec

/-- Bounds checked together in the hidden-input and unembedding row loop. -/
def WinURow (w : engine.Weights) (i : Nat) : Prop :=
  (∀ v ∈ w.win.val[i]!.val, -82 ≤ v.val ∧ v.val ≤ 82) ∧
  (∀ v ∈ w.u.val[i]!.val, -37 ≤ v.val ∧ v.val ≤ 37)

@[step]
theorem load_win_u_spec (w : engine.Weights) (valid : Bool) :
    engine.load_check_loop3 w valid 0#usize ⦃ r => r.1 = w ∧
      (r.2 = true → valid = true ∧ MatrixBound 82 w.win ∧ MatrixBound 37 w.u) ⦄ := by
  unfold engine.load_check_loop3
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 128 - s.2.val)
    (inv := fun s : Bool × Usize => s.2.val ≤ 128 ∧
      (s.1 = true → valid = true ∧ ∀ j < s.2.val, WinURow w j))
  · rintro ⟨b, i⟩ ⟨hi, hp⟩
    unfold engine.load_check_loop3.body
    dsimp only at hi hp ⊢
    split
    · rename_i hlt
      have hin : i.val < 128 := by scalar_tac
      step as ⟨wr, hwr⟩
      step as ⟨wb, hwb⟩
      split
      · rename_i hwt
        step as ⟨ur, hur⟩
        step as ⟨ub, hub⟩
        split
        · rename_i hut
          step as ⟨i1, hi1⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          intro hb
          obtain ⟨hv, hpre⟩ := hp hb
          refine ⟨hv, ?_⟩
          rw [hi1]
          intro j hj
          by_cases hj0 : j < i.val
          · exact hpre j hj0
          · have he : j = i.val := by omega
            subst j
            unfold WinURow
            simp only [getElem!_pos w.win.val i.val (by simpa using hin),
              getElem!_pos w.u.val i.val (by simpa using hin), ← hwr, ← hur]
            exact ⟨hwb hwt, hub hut⟩
        · step as ⟨i1, hi1⟩
          exact ⟨by scalar_tac, by simp, by scalar_tac⟩
      · step as ⟨i1, hi1⟩
        exact ⟨by scalar_tac, by simp, by scalar_tac⟩
    · simp only [WP.spec_ok]
      refine ⟨trivial, ?_⟩
      intro hb
      obtain ⟨hv, hpre⟩ := hp hb
      have hieq : i.val = 128 := by scalar_tac
      refine ⟨hv, ?_, ?_⟩
      · apply load_prefix_all
        intro j hj
        exact (hpre j (by simpa [hieq] using hj)).1
      · apply load_prefix_all
        intro j hj
        exact (hpre j (by simpa [hieq] using hj)).2
  · simp

/-- The head-wise load invariant includes all four projection matrices. -/
def LoadHead (w : engine.Weights) (h : Nat) : Prop :=
  MatrixBound 5 w.wq.val[h]! ∧ MatrixBound 22 w.wk.val[h]! ∧
  MatrixBound 106 w.wv.val[h]! ∧ MatrixBound 93 w.wo.val[h]!

@[step]
theorem load_heads_spec (w : engine.Weights) (valid : Bool) (i : Usize) :
    engine.load_check_loop2 w valid i 0#usize ⦃ r => r.1 = w ∧
      (r.2 = true → valid = true ∧ TensorBound 5 w.wq ∧ TensorBound 22 w.wk ∧
        TensorBound 106 w.wv ∧ TensorBound 93 w.wo) ⦄ := by
  unfold engine.load_check_loop2
  apply loop.spec_decr_nat
    (measure := fun s : engine.Weights × Bool × Usize × Usize => 4 - s.2.2.2.val)
    (inv := fun s : engine.Weights × Bool × Usize × Usize =>
      s.1 = w ∧ s.2.2.2.val ≤ 4 ∧
      (s.2.1 = true → valid = true ∧ ∀ j < s.2.2.2.val, LoadHead w j))
  · rintro ⟨w1, b, idx, h⟩ ⟨rfl, hh, hp⟩
    unfold engine.load_check_loop2.body
    dsimp only at hh hp ⊢
    split
    · have hh4 : h.val < 4 := by scalar_tac
      step as ⟨w2, b2, hw2, hb2⟩
      subst w2
      step as ⟨w3, b3, i3, hw3, hb3⟩
      subst w3
      step as ⟨h1, hh1⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro hb
      obtain ⟨hb2t, hwo⟩ := hb3 hb
      obtain ⟨hbt, hq, hk, hv⟩ := hb2 hb2t
      obtain ⟨hvalid, hpre⟩ := hp hbt
      refine ⟨hvalid, ?_⟩
      rw [hh1]
      intro j hj
      by_cases hj0 : j < h.val
      · exact hpre j hj0
      · have he : j = h.val := by omega
        subst j
        exact ⟨hq, hk, hv, hwo⟩
    · simp only [WP.spec_ok]
      refine ⟨trivial, ?_⟩
      intro hb
      obtain ⟨hv, hpre⟩ := hp hb
      have hheq : h.val = 4 := by scalar_tac
      refine ⟨hv, ?_, ?_, ?_, ?_⟩
      · apply load_prefix_all
        intro j hj
        exact (hpre j (by simpa [hheq] using hj)).1
      · apply load_prefix_all
        intro j hj
        exact (hpre j (by simpa [hheq] using hj)).2.1
      · apply load_prefix_all
        intro j hj
        exact (hpre j (by simpa [hheq] using hj)).2.2.1
      · apply load_prefix_all
        intro j hj
        exact (hpre j (by simpa [hheq] using hj)).2.2.2
  · simp

#print axioms load_win_u_spec
#print axioms load_heads_spec

/-- All entry bounds follow from successful execution of the translated loader. -/
theorem load_spec (w : engine.Weights) :
    engine.load_check w ⦃ b => b = true → LoadBounds w ⦄ := by
  unfold engine.load_check
  step as ⟨w1, v1, hw1, hv1⟩
  subst w1
  step as ⟨w2, v2, i2, hw2, hv2⟩
  subst w2
  step as ⟨w3, v3, hw3, hv3⟩
  subst w3
  step as ⟨w4, v4, hw4, hv4⟩
  subst w4
  step as ⟨w5, v5, hw5, hv5⟩
  subst w5
  split
  · rename_i hv5t
    obtain ⟨hv4t, hwout⟩ := hv5 hv5t
    obtain ⟨hv3t, hwin, hu⟩ := hv4 hv4t
    obtain ⟨hv2t, hq, hk, hv, ho⟩ := hv3 hv3t
    obtain ⟨hv1t, hpos⟩ := hv2 hv2t
    have htok := hv1 hv1t
    step as ⟨lbin, hlbin⟩
    have hc30 : ((1 : Int) <<< (30 : Nat)).bmod 18446744073709551616 = 1073741824 := by decide
    rw [I64.size_eq, hc30] at hlbin
    step as ⟨bbin, hbin⟩
    split
    · rename_i hbint
      step as ⟨lbout, hlbout⟩
      have hc37 : ((1 : Int) <<< (37 : Nat)).bmod 18446744073709551616 = 137438953472 := by decide
      rw [I64.size_eq, hc37] at hlbout
      step as ⟨bbout, hbout⟩
      split
      · rename_i hboutt
        step as ⟨bn, hn⟩
        split
        · rename_i hnt
          step as ⟨b2, h2⟩
          split
          · rename_i h2t
            step as ⟨b1, h1⟩
            split
            · rename_i h1t
              step as ⟨b0, h0⟩
              rename_i h0t
              exact ⟨htok, hpos, hq, hk, hv, ho, hwin, hwout, hu,
                by simpa [hlbin, Bounded] using hbin hbint,
                by simpa [hlbout, Bounded] using hbout hboutt,
                hn hnt, h2 h2t, h1 h1t, h0 h0t⟩
            · simp
          · simp
        · simp
      · simp
    · simp
  · simp

/-- Soundness of the actual load checker, with no assumed checker theorem. -/
theorem load_sound : LoadStage := by
  intro w hw
  have h := load_spec w
  simpa [hw] using h

#print axioms load_spec
#print axioms load_sound

end LcnExec.Engine
