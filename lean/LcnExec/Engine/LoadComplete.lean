import LcnExec.Engine.Stages

open Aeneas Aeneas.Std Result ControlFlow
namespace LcnExec.Engine

/-- Read a membership bound at a valid array index. -/
theorem load_complete_at {α : Type} [Inhabited α] {n : Usize}
    (xs : Array α n) (P : α → Prop) (hp : ∀ x ∈ xs.val, P x)
    (i : Nat) (hi : i < n.val) : P xs.val[i]! := by
  have hi' : i < xs.val.length := by simpa using hi
  simpa only [getElem!_pos xs.val i hi'] using hp xs.val[i] (List.getElem_mem hi')

@[step]
theorem bounded_i8_complete {n : Usize} (xs : Array I8 n) (limit : I8)
    (hl : 0 ≤ limit.val)
    (hb : ∀ v ∈ xs.val, -limit.val ≤ v.val ∧ v.val ≤ limit.val) :
    engine.bounded_i8 xs limit ⦃ b => b = true ⦄ := by
  unfold engine.bounded_i8 engine.bounded_i8_loop
  apply loop.spec_decr_nat
    (measure := fun i => n.val - i.val)
    (inv := fun i => i.val ≤ n.val)
  · intro i hi
    unfold engine.bounded_i8_loop.body
    split
    · have hin : i.val < n.val := by scalar_tac
      step as ⟨v, hv⟩
      have hvb := load_complete_at xs _ hb i.val hin
      have hvb' : -limit.val ≤ v.val ∧ v.val ≤ limit.val := by
        simpa only [getElem!_pos xs.val i.val (by simpa using hin), hv] using hvb
      step as ⟨neg, hn⟩
      split
      · scalar_tac
      · split
        · scalar_tac
        · step as ⟨i1, hi1⟩
          exact ⟨by omega, by omega⟩
    · simp
  · simp

@[step]
theorem bounded_i64_complete {n : Usize} (xs : Array I64 n) (limit : I64)
    (hl : 0 ≤ limit.val)
    (hb : ∀ v ∈ xs.val, -limit.val ≤ v.val ∧ v.val ≤ limit.val) :
    engine.bounded_i64 xs limit ⦃ b => b = true ⦄ := by
  unfold engine.bounded_i64 engine.bounded_i64_loop
  apply loop.spec_decr_nat
    (measure := fun i => n.val - i.val)
    (inv := fun i => i.val ≤ n.val)
  · intro i hi
    unfold engine.bounded_i64_loop.body
    split
    · have hin : i.val < n.val := by scalar_tac
      step as ⟨v, hv⟩
      have hvb := load_complete_at xs _ hb i.val hin
      have hvb' : -limit.val ≤ v.val ∧ v.val ≤ limit.val := by
        simpa only [getElem!_pos xs.val i.val (by simpa using hin), hv] using hvb
      step as ⟨neg, hn⟩
      split
      · scalar_tac
      · split
        · scalar_tac
        · step as ⟨i1, hi1⟩
          exact ⟨by omega, by omega⟩
    · simp
  · simp

@[step]
theorem table_complete {n : Usize} (xs : Array I64 n) (hb : TableBound xs) :
    engine.table xs ⦃ b => b = true ⦄ := by
  unfold engine.table engine.table_loop
  apply loop.spec_decr_nat
    (measure := fun i => n.val - i.val)
    (inv := fun i => i.val ≤ n.val)
  · intro i hi
    unfold engine.table_loop.body
    split
    · have hin : i.val < n.val := by scalar_tac
      step as ⟨v, hv⟩
      have hvb := load_complete_at xs _ hb i.val hin
      have hvb' : 0 ≤ v.val ∧ v.val ≤ 1073741824 := by
        simpa only [getElem!_pos xs.val i.val (by simpa using hin), hv] using hvb
      split
      · scalar_tac
      · simp only [engine.EXP_ONE]
        step as ⟨expOne, hexpOne⟩
        have hc : ((1 : Int) <<< (30 : Nat)).bmod 18446744073709551616 = 1073741824 := by decide
        rw [I64.size_eq, hc] at hexpOne
        split
        · scalar_tac
        · step as ⟨i1, hi1⟩
          exact ⟨by omega, by omega⟩
    · simp
  · simp

@[step]
theorem load_tok_complete (w : engine.Weights) (hb : MatrixBound 68 w.tok) :
    engine.load_check_loop0 w true 0#usize ⦃ r => r.1 = w ∧ r.2 = true ⦄ := by
  unfold engine.load_check_loop0
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 114 - s.2.val)
    (inv := fun s : Bool × Usize => s.1 = true ∧ s.2.val ≤ 114)
  · rintro ⟨b, i⟩ ⟨rfl, hi⟩
    unfold engine.load_check_loop0.body
    dsimp only at hi ⊢
    split
    · have hin : i.val < 114 := by scalar_tac
      step as ⟨row, hrow⟩
      have hr := load_complete_at w.tok _ hb i.val hin
      have hr' : ∀ v ∈ row.val, -(68 : Int) ≤ v.val ∧ v.val ≤ 68 := by
        simpa only [getElem!_pos w.tok.val i.val (by simpa using hin), hrow] using hr
      step as ⟨checked, hc⟩
      simp only [hc, ↓reduceIte]
      step as ⟨i1, hi1⟩
      exact ⟨by scalar_tac, by scalar_tac⟩
    · simp
  · simp

@[step]
theorem load_pos_complete (w : engine.Weights) (hb : MatrixBound 59 w.pos) :
    engine.load_check_loop1 w true 0#usize ⦃ r => r.1 = w ∧ r.2.1 = true ⦄ := by
  unfold engine.load_check_loop1
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 3 - s.2.val)
    (inv := fun s : Bool × Usize => s.1 = true ∧ s.2.val ≤ 3)
  · rintro ⟨b, i⟩ ⟨rfl, hi⟩
    unfold engine.load_check_loop1.body
    dsimp only at hi ⊢
    split
    · have hin : i.val < 3 := by scalar_tac
      step as ⟨row, hrow⟩
      have hr := load_complete_at w.pos _ hb i.val hin
      have hr' : ∀ v ∈ row.val, -(59 : Int) ≤ v.val ∧ v.val ≤ 59 := by
        simpa only [getElem!_pos w.pos.val i.val (by simpa using hin), hrow] using hr
      step as ⟨checked, hc⟩
      simp only [hc, ↓reduceIte]
      step as ⟨i1, hi1⟩
      exact ⟨by scalar_tac, by scalar_tac⟩
    · simp
  · simp

@[step]
theorem load_wout_complete (w : engine.Weights) (hb : MatrixBound 74 w.wout) :
    engine.load_check_loop4 w true 0#usize ⦃ r => r.1 = w ∧ r.2 = true ⦄ := by
  unfold engine.load_check_loop4
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 512 - s.2.val)
    (inv := fun s : Bool × Usize => s.1 = true ∧ s.2.val ≤ 512)
  · rintro ⟨b, i⟩ ⟨rfl, hi⟩
    unfold engine.load_check_loop4.body
    dsimp only at hi ⊢
    split
    · have hin : i.val < 512 := by scalar_tac
      step as ⟨row, hrow⟩
      have hr := load_complete_at w.wout _ hb i.val hin
      have hr' : ∀ v ∈ row.val, -(74 : Int) ≤ v.val ∧ v.val ≤ 74 := by
        simpa only [getElem!_pos w.wout.val i.val (by simpa using hin), hrow] using hr
      step as ⟨checked, hc⟩
      simp only [hc, ↓reduceIte]
      step as ⟨i1, hi1⟩
      exact ⟨by scalar_tac, by scalar_tac⟩
    · simp
  · simp


@[step]
theorem load_wo_complete (w : engine.Weights) (h : Usize) (hh : h.val < 4)
    (hb : MatrixBound 93 w.wo.val[h.val]!) :
    engine.load_check_loop2_loop1 w true 0#usize h ⦃ r => r.1 = w ∧ r.2.1 = true ⦄ := by
  unfold engine.load_check_loop2_loop1
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 32 - s.2.val)
    (inv := fun s : Bool × Usize => s.1 = true ∧ s.2.val ≤ 32)
  · rintro ⟨b, i⟩ ⟨rfl, hi⟩
    unfold engine.load_check_loop2_loop1.body
    dsimp only at hi ⊢
    split
    · have hin : i.val < 32 := by scalar_tac
      step as ⟨mat, hmat⟩
      have hm : w.wo.val[h.val]! = mat := by
        simpa only [getElem!_pos w.wo.val h.val (by simpa using hh)] using hmat.symm
      step as ⟨row, hrow⟩
      have hr := load_complete_at mat _ (show MatrixBound 93 mat by simpa only [hm] using hb) i.val hin
      have hr' : ∀ v ∈ row.val, -(93 : Int) ≤ v.val ∧ v.val ≤ 93 := by
        simpa only [getElem!_pos mat.val i.val (by simpa using hin), hrow] using hr
      step as ⟨checked, hc⟩
      simp only [hc, ↓reduceIte]
      step as ⟨i1, hi1⟩
      exact ⟨by scalar_tac, by scalar_tac⟩
    · simp
  · simp

@[step]
theorem load_qkv_complete (w : engine.Weights) (h : Usize) (hh : h.val < 4)
    (hq : MatrixBound 5 w.wq.val[h.val]!)
    (hk : MatrixBound 22 w.wk.val[h.val]!)
    (hv : MatrixBound 106 w.wv.val[h.val]!) :
    engine.load_check_loop2_loop0 w true 0#usize h ⦃ r => r.1 = w ∧ r.2 = true ⦄ := by
  unfold engine.load_check_loop2_loop0
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 128 - s.2.val)
    (inv := fun s : Bool × Usize => s.1 = true ∧ s.2.val ≤ 128)
  · rintro ⟨b, i⟩ ⟨rfl, hi⟩
    unfold engine.load_check_loop2_loop0.body
    dsimp only at hi ⊢
    split
    · have hin : i.val < 128 := by scalar_tac
      step as ⟨qm, hqm⟩
      have hqm' : w.wq.val[h.val]! = qm := by
        simpa only [getElem!_pos w.wq.val h.val (by simpa using hh)] using hqm.symm
      step as ⟨qr, hqr⟩
      have hqr' := load_complete_at qm _ (show MatrixBound 5 qm by simpa only [hqm'] using hq) i.val hin
      have hqr'' : ∀ v ∈ qr.val, -(5 : Int) ≤ v.val ∧ v.val ≤ 5 := by
        simpa only [getElem!_pos qm.val i.val (by simpa using hin), hqr] using hqr'
      step as ⟨qb, hqb⟩
      simp only [hqb, ↓reduceIte]
      step as ⟨km, hkm⟩
      have hkm' : w.wk.val[h.val]! = km := by
        simpa only [getElem!_pos w.wk.val h.val (by simpa using hh)] using hkm.symm
      step as ⟨kr, hkr⟩
      have hkr' := load_complete_at km _ (show MatrixBound 22 km by simpa only [hkm'] using hk) i.val hin
      have hkr'' : ∀ v ∈ kr.val, -(22 : Int) ≤ v.val ∧ v.val ≤ 22 := by
        simpa only [getElem!_pos km.val i.val (by simpa using hin), hkr] using hkr'
      step as ⟨kb, hkb⟩
      simp only [hkb, ↓reduceIte]
      step as ⟨vm, hvm⟩
      have hvm' : w.wv.val[h.val]! = vm := by
        simpa only [getElem!_pos w.wv.val h.val (by simpa using hh)] using hvm.symm
      step as ⟨vr, hvr⟩
      have hvr' := load_complete_at vm _ (show MatrixBound 106 vm by simpa only [hvm'] using hv) i.val hin
      have hvr'' : ∀ v ∈ vr.val, -(106 : Int) ≤ v.val ∧ v.val ≤ 106 := by
        simpa only [getElem!_pos vm.val i.val (by simpa using hin), hvr] using hvr'
      step as ⟨vb, hvb⟩
      simp only [hvb, ↓reduceIte]
      step as ⟨i1, hi1⟩
      exact ⟨by scalar_tac, by scalar_tac⟩
    · simp
  · simp

@[step]
theorem load_win_u_complete (w : engine.Weights)
    (hw : MatrixBound 82 w.win) (hu : MatrixBound 37 w.u) :
    engine.load_check_loop3 w true 0#usize ⦃ r => r.1 = w ∧ r.2 = true ⦄ := by
  unfold engine.load_check_loop3
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 128 - s.2.val)
    (inv := fun s : Bool × Usize => s.1 = true ∧ s.2.val ≤ 128)
  · rintro ⟨b, i⟩ ⟨rfl, hi⟩
    unfold engine.load_check_loop3.body
    dsimp only at hi ⊢
    split
    · have hin : i.val < 128 := by scalar_tac
      step as ⟨wr, hwr⟩
      have hwr' := load_complete_at w.win _ hw i.val hin
      have hwr'' : ∀ v ∈ wr.val, -(82 : Int) ≤ v.val ∧ v.val ≤ 82 := by
        simpa only [getElem!_pos w.win.val i.val (by simpa using hin), hwr] using hwr'
      step as ⟨wb, hwb⟩
      simp only [hwb, ↓reduceIte]
      step as ⟨ur, hur⟩
      have hur' := load_complete_at w.u _ hu i.val hin
      have hur'' : ∀ v ∈ ur.val, -(37 : Int) ≤ v.val ∧ v.val ≤ 37 := by
        simpa only [getElem!_pos w.u.val i.val (by simpa using hin), hur] using hur'
      step as ⟨ub, hub⟩
      simp only [hub, ↓reduceIte]
      step as ⟨i1, hi1⟩
      exact ⟨by scalar_tac, by scalar_tac⟩
    · simp
  · simp

@[step]
theorem load_heads_complete (w : engine.Weights) (idx : Usize)
    (hq : TensorBound 5 w.wq) (hk : TensorBound 22 w.wk)
    (hv : TensorBound 106 w.wv) (ho : TensorBound 93 w.wo) :
    engine.load_check_loop2 w true idx 0#usize ⦃ r => r.1 = w ∧ r.2 = true ⦄ := by
  unfold engine.load_check_loop2
  apply loop.spec_decr_nat
    (measure := fun s : engine.Weights × Bool × Usize × Usize => 4 - s.2.2.2.val)
    (inv := fun s : engine.Weights × Bool × Usize × Usize =>
      s.1 = w ∧ s.2.1 = true ∧ s.2.2.2.val ≤ 4)
  · rintro ⟨w1, b, i, h⟩ ⟨hw1, hb, hh⟩
    dsimp only at hw1 hb hh ⊢
    subst w1
    subst b
    unfold engine.load_check_loop2.body
    split
    · have hh4 : h.val < 4 := by scalar_tac
      have hq' := load_complete_at w.wq _ hq h.val hh4
      have hk' := load_complete_at w.wk _ hk h.val hh4
      have hv' := load_complete_at w.wv _ hv h.val hh4
      have ho' := load_complete_at w.wo _ ho h.val hh4
      step as ⟨w2, b2, hw2, hb2⟩
      subst w2
      subst b2
      step as ⟨w3, b3, i3, hw3, hb3⟩
      subst w3
      subst b3
      step as ⟨h1, hh1⟩
      exact ⟨by scalar_tac, by scalar_tac⟩
    · simp
  · simp

/-- Completeness of all load-check stages, without evaluating the translated loops. -/
theorem load_complete_spec (w : engine.Weights) (hb : LoadBounds w) :
    engine.load_check w ⦃ b => b = true ⦄ := by
  unfold engine.load_check
  have htok := hb.tok
  have hpos := hb.pos
  have hq := hb.wq
  have hk := hb.wk
  have hv := hb.wv
  have ho := hb.wo
  have hwin := hb.win
  have hu := hb.u
  have hwout := hb.wout
  step as ⟨w1, v1, hw1, hv1⟩
  subst w1
  subst v1
  step as ⟨w2, v2, i2, hw2, hv2⟩
  subst w2
  subst v2
  step as ⟨w3, v3, hw3, hv3⟩
  subst w3
  subst v3
  step as ⟨w4, v4, hw4, hv4⟩
  subst w4
  subst v4
  step as ⟨w5, v5, hw5, hv5⟩
  subst w5
  subst v5
  simp only [↓reduceIte]
  step as ⟨lbin, hlbin⟩
  have hc30 : ((1 : Int) <<< (30 : Nat)).bmod 18446744073709551616 = 1073741824 := by decide
  rw [I64.size_eq, hc30] at hlbin
  have hbin : ∀ v ∈ w.bin.val, -lbin.val ≤ v.val ∧ v.val ≤ lbin.val := by
    simpa only [hlbin, Bounded] using hb.bin
  step as ⟨bbin, hbbin⟩
  simp only [hbbin, ↓reduceIte]
  step as ⟨lbout, hlbout⟩
  have hc37 : ((1 : Int) <<< (37 : Nat)).bmod 18446744073709551616 = 137438953472 := by decide
  rw [I64.size_eq, hc37] at hlbout
  have hbout : ∀ v ∈ w.bout.val, -lbout.val ≤ v.val ∧ v.val ≤ lbout.val := by
    simpa only [hlbout, Bounded] using hb.bout
  step as ⟨bbout, hbbout⟩
  simp only [hbbout, ↓reduceIte]
  have hn := hb.exp_n
  have h2 := hb.exp_2
  have h1 := hb.exp_1
  have h0 := hb.exp_0
  step as ⟨bn, hbn⟩
  simp only [hbn, ↓reduceIte]
  step as ⟨b2, hb2⟩
  simp only [hb2, ↓reduceIte]
  step as ⟨b1, hb1⟩
  simp only [hb1, ↓reduceIte]
  step as ⟨b0, hb0⟩
  exact hb0

/-- Generic load-check completeness from the exact stored-coordinate envelopes. -/
theorem load_complete (w : engine.Weights) (hb : LoadBounds w) :
    engine.load_check w = ok true := by
  have h := load_complete_spec w hb
  cases heq : engine.load_check w with
  | ret b => simpa [heq] using h
  | vis e k => simp [heq] at h
  | div => simp [heq] at h

#print axioms load_complete
end LcnExec.Engine
