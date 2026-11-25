import LcnExec.GeneralEngine.View

open Aeneas Aeneas.Std Result ControlFlow
namespace LcnExec.GeneralEngine

/-! ## Soundness of the translated load checker

`general_engine.load_check W = ok true` implies every entry bound of `LoadBounds W`,
including both layers (active and padding). -/

/-- The all-default layer, so `getElem!` is defined on layer lists. -/
instance : Inhabited general_engine.LayerWeights where
  default :=
    { wq := default, wk := default, wv := default, wo := default,
      win := default, bin := default, wout := default, bout := default }

/-- Total correctness and soundness of the translated byte-vector checker. -/
@[step]
theorem bounded_i8_spec {n : Usize} (xs : Array I8 n) (limit : I8)
    (hl : 0 ≤ limit.val) :
    general_engine.bounded_i8 xs limit ⦃ b => b = true →
      ∀ v ∈ xs.val, -limit.val ≤ v.val ∧ v.val ≤ limit.val ⦄ := by
  unfold general_engine.bounded_i8 general_engine.bounded_i8_loop
  apply loop.spec_decr_nat
    (measure := fun i => n.val - i.val)
    (inv := fun i => i.val ≤ n.val ∧
      ∀ j : Nat, j < i.val → -limit.val ≤ xs.val[j]!.val ∧ xs.val[j]!.val ≤ limit.val)
  · intro i
    rintro ⟨hi, hp⟩
    unfold general_engine.bounded_i8_loop.body
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
            simpa only [getElem!_pos xs.val i.val (by simpa using hin), hv] using
              (show -limit.val ≤ v.val ∧ v.val ≤ limit.val by scalar_tac)
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
    general_engine.bounded_i64 xs limit ⦃ b => b = true →
      ∀ v ∈ xs.val, -limit.val ≤ v.val ∧ v.val ≤ limit.val ⦄ := by
  unfold general_engine.bounded_i64 general_engine.bounded_i64_loop
  apply loop.spec_decr_nat
    (measure := fun i => n.val - i.val)
    (inv := fun i => i.val ≤ n.val ∧
      ∀ j : Nat, j < i.val → -limit.val ≤ xs.val[j]!.val ∧ xs.val[j]!.val ≤ limit.val)
  · intro i
    rintro ⟨hi, hp⟩
    unfold general_engine.bounded_i64_loop.body
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
            simpa only [getElem!_pos xs.val i.val (by simpa using hin), hv] using
              (show -limit.val ≤ v.val ∧ v.val ≤ limit.val by scalar_tac)
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
    general_engine.table xs ⦃ b => b = true →
      ∀ v ∈ xs.val, 0 ≤ v.val ∧ v.val ≤ 1073741824 ⦄ := by
  unfold general_engine.table general_engine.table_loop
  apply loop.spec_decr_nat
    (measure := fun i => n.val - i.val)
    (inv := fun i => i.val ≤ n.val ∧
      ∀ j : Nat, j < i.val → 0 ≤ xs.val[j]!.val ∧ xs.val[j]!.val ≤ 1073741824)
  · intro i
    rintro ⟨hi, hp⟩
    unfold general_engine.table_loop.body
    split
    · rename_i hlt
      have hin : i.val < n.val := by scalar_tac
      step as ⟨v, hv⟩
      split
      · simp
      · rename_i hlo
        simp only [general_engine.EXP_ONE]
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
            simpa only [getElem!_pos xs.val i.val (by simpa using hin), hv] using
              (show 0 ≤ v.val ∧ v.val ≤ 1073741824 by scalar_tac)
    · simp only [WP.spec_ok]
      intro _ v hv
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
      have hlen : xs.val.length = n.val := by simp
      have hi' : i.val = n.val := by scalar_tac
      simpa only [getElem!_pos xs.val j hj] using hp j (by omega)
  · simp

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

/-- Bounds checked for one Q/K/V input coordinate. -/
def QkvRow (layer : general_engine.LayerWeights) (h i : Nat) : Prop :=
  (∀ v ∈ layer.wq.val[h]!.val[i]!.val, -5 ≤ v.val ∧ v.val ≤ 5) ∧
  (∀ v ∈ layer.wk.val[h]!.val[i]!.val, -22 ≤ v.val ∧ v.val ≤ 22) ∧
  (∀ v ∈ layer.wv.val[h]!.val[i]!.val, -106 ≤ v.val ∧ v.val ≤ 106)

@[step]
theorem layer_qkv_spec (layer : general_engine.LayerWeights) (valid : Bool) (h : Usize)
    (hh : h.val < 4) :
    general_engine.layer_load_check_loop0_loop0 layer valid h 0#usize ⦃ r =>
      r.1 = layer ∧ (r.2 = true → valid = true ∧
        MatrixBound 5 layer.wq.val[h.val]! ∧ MatrixBound 22 layer.wk.val[h.val]! ∧
        MatrixBound 106 layer.wv.val[h.val]!) ⦄ := by
  unfold general_engine.layer_load_check_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 128 - s.2.val)
    (inv := fun s : Bool × Usize => s.2.val ≤ 128 ∧
      (s.1 = true → valid = true ∧ ∀ j < s.2.val, QkvRow layer h.val j))
  · rintro ⟨b, i⟩ ⟨hi, hp⟩
    unfold general_engine.layer_load_check_loop0_loop0.body
    dsimp only at hi hp ⊢
    simp only [general_engine.D_MODEL]
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
              have hqm! : layer.wq.val[h.val]! = qm := by
                simpa only [getElem!_pos layer.wq.val h.val (by simpa using hh)] using hqm.symm
              have hkm! : layer.wk.val[h.val]! = km := by
                simpa only [getElem!_pos layer.wk.val h.val (by simpa using hh)] using hkm.symm
              have hvm! : layer.wv.val[h.val]! = vm := by
                simpa only [getElem!_pos layer.wv.val h.val (by simpa using hh)] using hvm.symm
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

@[step]
theorem layer_wo_spec (layer : general_engine.LayerWeights) (valid : Bool) (h : Usize)
    (hh : h.val < 4) :
    general_engine.layer_load_check_loop0_loop1 layer valid h 0#usize ⦃ r =>
      r.1 = layer ∧ (r.2 = true → valid = true ∧
        MatrixBound 93 (layer.wo.val[h.val]!)) ⦄ := by
  unfold general_engine.layer_load_check_loop0_loop1
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 32 - s.2.val)
    (inv := fun s : Bool × Usize => s.2.val ≤ 32 ∧
      (s.1 = true → valid = true ∧
        ∀ j < s.2.val, ∀ v ∈ (layer.wo.val[h.val]!).val[j]!.val, -93 ≤ v.val ∧ v.val ≤ 93))
  · rintro ⟨b, i⟩ ⟨hi, hp⟩
    unfold general_engine.layer_load_check_loop0_loop1.body
    dsimp only at hi hp ⊢
    simp only [general_engine.D_HEAD]
    split
    · rename_i hlt
      have hin : i.val < 32 := by scalar_tac
      step as ⟨mat, hmat⟩
      step as ⟨row, hrow⟩
      have hmat! : layer.wo.val[h.val]! = mat := by
        simpa only [getElem!_pos layer.wo.val h.val (by simpa using hh)] using hmat.symm
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
          ∀ v ∈ row.val, -93 ≤ v.val ∧ v.val ≤ 93) (layer.wo.val[h.val]!).val i.val hpre
        simpa only [hmat!, getElem!_pos mat.val i.val (by simpa using hin), ← hrow] using
          hc hchecked
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

/-- The head-wise layer load invariant includes all four projection matrices. -/
def LayerHead (layer : general_engine.LayerWeights) (h : Nat) : Prop :=
  MatrixBound 5 layer.wq.val[h]! ∧ MatrixBound 22 layer.wk.val[h]! ∧
  MatrixBound 106 layer.wv.val[h]! ∧ MatrixBound 93 layer.wo.val[h]!

@[step]
theorem layer_heads_spec (layer : general_engine.LayerWeights) (valid : Bool) :
    general_engine.layer_load_check_loop0 layer valid 0#usize ⦃ r =>
      r.1 = layer ∧ (r.2 = true → valid = true ∧
        TensorBound 5 layer.wq ∧ TensorBound 22 layer.wk ∧
        TensorBound 106 layer.wv ∧ TensorBound 93 layer.wo) ⦄ := by
  unfold general_engine.layer_load_check_loop0
  apply loop.spec_decr_nat
    (measure := fun s : general_engine.LayerWeights × Bool × Usize => 4 - s.2.2.val)
    (inv := fun s : general_engine.LayerWeights × Bool × Usize =>
      s.1 = layer ∧ s.2.2.val ≤ 4 ∧
      (s.2.1 = true → valid = true ∧ ∀ j < s.2.2.val, LayerHead layer j))
  · rintro ⟨layer1, b, h⟩ ⟨rfl, hh, hp⟩
    unfold general_engine.layer_load_check_loop0.body
    dsimp only at hh hp ⊢
    simp only [general_engine.N_HEADS]
    split
    · have hh4 : h.val < 4 := by scalar_tac
      step as ⟨layer2, b2, hl2, hb2⟩
      step as ⟨layer3, b3, hl3, hb3⟩
      step as ⟨h1, hh1⟩
      subst layer2
      subst layer3
      refine ⟨rfl, by omega, ?_, by omega⟩
      intro hb
      obtain ⟨hb3t, hwo⟩ := hb3 hb
      obtain ⟨hb2t, hq, hk, hv⟩ := hb2 hb3t
      obtain ⟨hvalid, hpre⟩ := hp hb2t
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

@[step]
theorem layer_win_spec (layer : general_engine.LayerWeights) (valid : Bool) :
    general_engine.layer_load_check_loop1 layer valid 0#usize ⦃ r =>
      r.1 = layer ∧ (r.2 = true → valid = true ∧ MatrixBound 82 layer.win) ⦄ := by
  unfold general_engine.layer_load_check_loop1
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 128 - s.2.val)
    (inv := fun s : Bool × Usize => s.2.val ≤ 128 ∧
      (s.1 = true → valid = true ∧
        ∀ j < s.2.val, ∀ v ∈ layer.win.val[j]!.val, -82 ≤ v.val ∧ v.val ≤ 82))
  · rintro ⟨b, i⟩ ⟨hi, hp⟩
    unfold general_engine.layer_load_check_loop1.body
    dsimp only at hi hp ⊢
    simp only [general_engine.D_MODEL]
    split
    · rename_i hlt
      have hin : i.val < 128 := by scalar_tac
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
        apply load_prefix_succ (fun row : Array I8 512#usize =>
          ∀ v ∈ row.val, -82 ≤ v.val ∧ v.val ≤ 82) layer.win.val i.val hpre
        simpa only [getElem!_pos layer.win.val i.val (by simpa using hin), ← hrow] using
          hc hchecked
      · step as ⟨i1, hi1⟩
        exact ⟨by scalar_tac, by simp, by scalar_tac⟩
    · simp only [WP.spec_ok]
      refine ⟨trivial, ?_⟩
      intro hb
      obtain ⟨hv, hpre⟩ := hp hb
      refine ⟨hv, ?_⟩
      apply load_prefix_all
      have hieq : i.val = 128 := by scalar_tac
      simpa [hieq] using hpre
  · simp

@[step]
theorem layer_wout_spec (layer : general_engine.LayerWeights) (valid : Bool) :
    general_engine.layer_load_check_loop2 layer valid 0#usize ⦃ r =>
      r.1 = layer ∧ (r.2 = true → valid = true ∧ MatrixBound 74 layer.wout) ⦄ := by
  unfold general_engine.layer_load_check_loop2
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 512 - s.2.val)
    (inv := fun s : Bool × Usize => s.2.val ≤ 512 ∧
      (s.1 = true → valid = true ∧
        ∀ j < s.2.val, ∀ v ∈ layer.wout.val[j]!.val, -74 ≤ v.val ∧ v.val ≤ 74))
  · rintro ⟨b, i⟩ ⟨hi, hp⟩
    unfold general_engine.layer_load_check_loop2.body
    dsimp only at hi hp ⊢
    simp only [general_engine.D_MLP]
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
          ∀ v ∈ row.val, -74 ≤ v.val ∧ v.val ≤ 74) layer.wout.val i.val hpre
        simpa only [getElem!_pos layer.wout.val i.val (by simpa using hin), ← hrow] using
          hc hchecked
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

/-- All entry bounds of one layer follow from successful layer execution. -/
@[step]
theorem layer_load_check_spec (layer : general_engine.LayerWeights) :
    general_engine.layer_load_check layer ⦃ b => b = true → LayerBounds layer ⦄ := by
  unfold general_engine.layer_load_check
  step as ⟨layer1, v1, hl1, hv1⟩
  subst layer1
  step as ⟨layer2, v2, hl2, hv2⟩
  subst layer2
  step as ⟨layer3, v3, hl3, hv3⟩
  subst layer3
  split
  · rename_i hv3t
    obtain ⟨hv2t, hwout⟩ := hv3 hv3t
    obtain ⟨hv1t, hwin⟩ := hv2 hv2t
    obtain ⟨hq, hk, hv, ho⟩ := hv1 hv1t
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
      rename_i hboutt
      exact ⟨hq, hk, hv, ho, hwin, hwout,
        by simpa [hlbin, Bounded] using hbin hbint,
        by simpa [hlbout, Bounded] using hbout hboutt⟩
    · simp
  · simp

@[step]
theorem load_tok_spec (w : general_engine.Weights) (valid : Bool) :
    general_engine.load_check_loop0 w.tok valid 0#usize ⦃ r =>
      (r = true → valid = true ∧ MatrixBound 68 w.tok) ⦄ := by
  unfold general_engine.load_check_loop0
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 256 - s.2.val)
    (inv := fun s : Bool × Usize => s.2.val ≤ 256 ∧
      (s.1 = true → valid = true ∧
        ∀ j < s.2.val, ∀ v ∈ w.tok.val[j]!.val, -68 ≤ v.val ∧ v.val ≤ 68))
  · rintro ⟨b, i⟩ ⟨hi, hp⟩
    unfold general_engine.load_check_loop0.body
    dsimp only at hi hp ⊢
    simp only [general_engine.VOCAB]
    split
    · rename_i hlt
      have hin : i.val < 256 := by scalar_tac
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
        simpa only [getElem!_pos w.tok.val i.val (by simpa using hin), ← hrow] using
          hc hchecked
      · step as ⟨i1, hi1⟩
        exact ⟨by scalar_tac, by simp, by scalar_tac⟩
    · simp only [WP.spec_ok]
      intro hb
      obtain ⟨hv, hpre⟩ := hp hb
      refine ⟨hv, ?_⟩
      apply load_prefix_all
      have hieq : i.val = 256 := by scalar_tac
      simpa [hieq] using hpre
  · simp

@[step]
theorem load_pos_spec (w : general_engine.Weights) (valid : Bool) :
    general_engine.load_check_loop1 w.pos valid 0#usize ⦃ r =>
      (r = true → valid = true ∧ MatrixBound 59 w.pos) ⦄ := by
  unfold general_engine.load_check_loop1
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 32 - s.2.val)
    (inv := fun s : Bool × Usize => s.2.val ≤ 32 ∧
      (s.1 = true → valid = true ∧
        ∀ j < s.2.val, ∀ v ∈ w.pos.val[j]!.val, -59 ≤ v.val ∧ v.val ≤ 59))
  · rintro ⟨b, i⟩ ⟨hi, hp⟩
    unfold general_engine.load_check_loop1.body
    dsimp only at hi hp ⊢
    simp only [general_engine.MAX_SEQ]
    split
    · rename_i hlt
      have hin : i.val < 32 := by scalar_tac
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
        simpa only [getElem!_pos w.pos.val i.val (by simpa using hin), ← hrow] using
          hc hchecked
      · step as ⟨i1, hi1⟩
        exact ⟨by scalar_tac, by simp, by scalar_tac⟩
    · simp only [WP.spec_ok]
      intro hb
      obtain ⟨hv, hpre⟩ := hp hb
      refine ⟨hv, ?_⟩
      apply load_prefix_all
      have hieq : i.val = 32 := by scalar_tac
      simpa [hieq] using hpre
  · simp

@[step]
theorem load_layers_spec (w : general_engine.Weights) (valid : Bool) :
    general_engine.load_check_loop2 w.layers valid 0#usize ⦃ r =>
      (r = true → valid = true ∧ ∀ L ∈ w.layers.val, LayerBounds L) ⦄ := by
  unfold general_engine.load_check_loop2
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 2 - s.2.val)
    (inv := fun s : Bool × Usize => s.2.val ≤ 2 ∧
      (s.1 = true → valid = true ∧ ∀ j < s.2.val, LayerBounds (w.layers.val[j]!)))
  · rintro ⟨b, l⟩ ⟨hi, hp⟩
    unfold general_engine.load_check_loop2.body
    dsimp only at hi hp ⊢
    simp only [general_engine.MAX_LAYERS]
    split
    · rename_i hlt
      have hin : l.val < 2 := by scalar_tac
      step as ⟨lw, hlw⟩
      step as ⟨checked, hc⟩
      split
      · rename_i hchecked
        step as ⟨l1, hi1⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro hb
        obtain ⟨hv, hpre⟩ := hp hb
        refine ⟨hv, ?_⟩
        rw [hi1]
        apply load_prefix_succ (fun L => LayerBounds L) w.layers.val l.val hpre
        simpa only [getElem!_pos w.layers.val l.val (by simpa using hin), ← hlw] using
          hc hchecked
      · step as ⟨l1, hi1⟩
        exact ⟨by scalar_tac, by simp, by scalar_tac⟩
    · simp only [WP.spec_ok]
      intro hb
      obtain ⟨hv, hpre⟩ := hp hb
      refine ⟨hv, ?_⟩
      apply load_prefix_all
      have hieq : l.val = 2 := by scalar_tac
      simpa [hieq] using hpre
  · simp

@[step]
theorem load_u_spec (w : general_engine.Weights) (valid : Bool) :
    general_engine.load_check_loop3 w.u valid 0#usize ⦃ r =>
      (r = true → valid = true ∧ MatrixBound 37 w.u) ⦄ := by
  unfold general_engine.load_check_loop3
  apply loop.spec_decr_nat
    (measure := fun s : Bool × Usize => 128 - s.2.val)
    (inv := fun s : Bool × Usize => s.2.val ≤ 128 ∧
      (s.1 = true → valid = true ∧
        ∀ j < s.2.val, ∀ v ∈ w.u.val[j]!.val, -37 ≤ v.val ∧ v.val ≤ 37))
  · rintro ⟨b, i⟩ ⟨hi, hp⟩
    unfold general_engine.load_check_loop3.body
    dsimp only at hi hp ⊢
    simp only [general_engine.D_MODEL]
    split
    · rename_i hlt
      have hin : i.val < 128 := by scalar_tac
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
        apply load_prefix_succ (fun row : Array I8 256#usize =>
          ∀ v ∈ row.val, -37 ≤ v.val ∧ v.val ≤ 37) w.u.val i.val hpre
        simpa only [getElem!_pos w.u.val i.val (by simpa using hin), ← hrow] using
          hc hchecked
      · step as ⟨i1, hi1⟩
        exact ⟨by scalar_tac, by simp, by scalar_tac⟩
    · simp only [WP.spec_ok]
      intro hb
      obtain ⟨hv, hpre⟩ := hp hb
      refine ⟨hv, ?_⟩
      apply load_prefix_all
      have hieq : i.val = 128 := by scalar_tac
      simpa [hieq] using hpre
  · simp

/-- The leading scalar guard chain of `load_check` never fails; its value is irrelevant
to the entry bounds. -/
theorem load_scalars_spec (w : general_engine.Weights) :
    (if w.n_layers >= 1#usize
      then
        if w.n_layers <= general_engine.MAX_LAYERS
        then
          if w.vocab_size >= 1#usize
          then ok (decide (w.vocab_size <= general_engine.VOCAB))
          else ok false
        else ok false
      else ok false) ⦃ _ => True ⦄ := by
  split
  · split
    · split
      · simp
      · simp
    · simp
  · simp

/-- All entry bounds follow from successful execution of the translated loader. -/
theorem load_spec (w : general_engine.Weights) :
    general_engine.load_check w ⦃ b => b = true → LoadBounds w ⦄ := by
  unfold general_engine.load_check
  refine Aeneas.Std.WP.spec_bind (load_scalars_spec w) ?_
  intro valid _
  step as ⟨v1, hv1⟩
  step as ⟨v2, hv2⟩
  step as ⟨v3, hv3⟩
  step as ⟨v4, hv4⟩
  split
  · rename_i hv4t
    obtain ⟨hv3t, hu⟩ := hv4 hv4t
    obtain ⟨hv2t, hlayers⟩ := hv3 hv3t
    obtain ⟨hv1t, hpos⟩ := hv2 hv2t
    have htok := hv1 hv1t
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
          exact ⟨htok.2, hpos, hlayers, hu, hn hnt, h2 h2t, h1 h1t, h0 h0t⟩
        · simp
      · simp
    · simp
  · simp

/-- Soundness of the actual load checker, with no assumed checker theorem. -/
theorem load_sound (w : general_engine.Weights)
    (hw : general_engine.load_check w = ok true) : LoadBounds w := by
  have h := load_spec w
  simpa [hw] using h

end LcnExec.GeneralEngine
