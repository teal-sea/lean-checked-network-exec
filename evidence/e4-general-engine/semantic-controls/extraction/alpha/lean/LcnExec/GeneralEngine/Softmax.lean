import LcnExec.GeneralEngine.Primitives
import LcnExec.GeneralEngine.Load

open Aeneas Aeneas.Std Result ControlFlow
namespace LcnExec.GeneralEngine

/-! ## The causal softmax over positions `0..p`

The three translated Rust loops of `softmax_at` generalize the one-layer engine's softmax
from three fixed positions to any `p < 32`: the running maximum, the exact exponential
table scan with its running denominator, and the rounded weights. -/

/-- The running maximum scan over the first `j` scores, as the Rust loop computes it. -/
def softMaxScan (s : List Int) (j : Nat) : Int :=
  (List.range j).foldl
    (fun m k => if GeneralModel.nth 0 s k > m then GeneralModel.nth 0 s k else m)
    (GeneralModel.nth 0 s 0)

/-- One exact exponential entry: `expFix (smax - s[j])`. -/
def softEsAt (W : GeneralModel.Weights) (s : List Int) (smax : Int) (j : Nat) : Int :=
  GeneralModel.expFix W (smax - GeneralModel.nth 0 s j)

/-- The exact exponential entries over the first `p + 1` scores, given the maximum. -/
def softEs (W : GeneralModel.Weights) (s : List Int) (smax : Int) (p : Nat) : List Int :=
  (List.range (p + 1)).map (softEsAt W s smax)

theorem softEs_length (W : GeneralModel.Weights) (s : List Int) (smax : Int) (p : Nat) :
    (softEs W s smax p).length = p + 1 := by
  simp [softEs]

theorem softEs_getElem (W : GeneralModel.Weights) (s : List Int) (smax : Int) (p j : Nat)
    (hj : j < p + 1) : (softEs W s smax p)[j]'(by simpa [softEs_length] using hj) =
    softEsAt W s smax j := by
  simp only [softEs, List.getElem_map, List.getElem_range]

theorem ints_length32 (s : Array I64 32#usize) : (ints s).length = 32 := by
  simp [ints]

theorem getElem_ints (s : Array I64 32#usize) (j : Nat) (hj : j < 32) :
    (ints s)[j]'(by rw [ints_length32]; exact hj) = (s.val[j]!).val := by
  have hl : s.val.length = 32 := by simp
  have hpos : j < s.val.length := by omega
  have heq : s.val[j]! = s.val[j]'(hpos) := getElem!_pos s.val j hpos
  simp [ints, heq]

theorem ints_get_bound (e : Array I64 32#usize) (lo hi : Int)
    (hlo : ∀ v ∈ e.val, lo ≤ v.val) (hhi : ∀ v ∈ e.val, v.val ≤ hi)
    (j : Nat) (hj : j < 32) :
    lo ≤ (ints e)[j]'(by rw [ints_length32]; exact hj) ∧
    (ints e)[j]'(by rw [ints_length32]; exact hj) ≤ hi := by
  have hl : e.val.length = 32 := by simp
  have hmem : e.val[j]'(by omega) ∈ e.val := List.getElem_mem (by omega)
  have hb1 := hlo _ hmem
  have hb2 := hhi _ hmem
  simp only [ints, List.getElem_map] at hb1 hb2 ⊢
  exact ⟨hb1, hb2⟩

theorem soft_max_scan_one (s : List Int) : softMaxScan s 1 = GeneralModel.nth 0 s 0 := by
  simp [softMaxScan]

theorem soft_max_scan_succ (s : List Int) (j : Nat) :
    softMaxScan s (j + 1) =
      (if GeneralModel.nth 0 s j > softMaxScan s j then GeneralModel.nth 0 s j
        else softMaxScan s j) := by
  simp only [softMaxScan, List.range_succ, List.foldl_append]
  rfl

/-- The scan always stops on one of the scanned scores. -/
theorem soft_max_scan_attained (s : List Int) : ∀ m : Nat, 0 < m →
    ∃ j < m, GeneralModel.nth 0 s j = softMaxScan s m
  | 0, hm => by omega
  | m + 1, hm => by
    have hstep : softMaxScan s (m + 1) =
        (if GeneralModel.nth 0 s m > softMaxScan s m then GeneralModel.nth 0 s m
          else softMaxScan s m) := soft_max_scan_succ s m
    by_cases hlt : GeneralModel.nth 0 s m > softMaxScan s m
    · refine ⟨m, by omega, ?_⟩
      rw [hstep, if_pos hlt]
    · have hprev : 0 < m ∨ m = 0 := by omega
      rcases hprev with hm0 | hm0
      · obtain ⟨j, hj, hje⟩ := soft_max_scan_attained s m hm0
        refine ⟨j, by omega, ?_⟩
        rw [hstep, if_neg hlt, hje]
      · subst hm0
        refine ⟨0, by omega, ?_⟩
        rw [hstep, if_neg hlt]
        simp [softMaxScan, GeneralModel.nth]

/-- Every scanned score is at most the scan result. -/
theorem soft_max_scan_ge (s : List Int) : ∀ (j j' : Nat), j' < j →
    GeneralModel.nth 0 s j' ≤ softMaxScan s j
  | 0, _, hj' => by omega
  | j + 1, j', hj' => by
    have hstep : softMaxScan s (j + 1) =
        (if GeneralModel.nth 0 s j > softMaxScan s j then GeneralModel.nth 0 s j
          else softMaxScan s j) := soft_max_scan_succ s j
    by_cases hlt : GeneralModel.nth 0 s j > softMaxScan s j
    · rw [hstep, if_pos hlt]
      by_cases hjj : j' = j
      · subst hjj
        omega
      · have hprev := soft_max_scan_ge s j j' (by omega)
        omega
    · rw [hstep, if_neg hlt]
      by_cases hjj : j' = j
      · subst hjj
        omega
      · exact soft_max_scan_ge s j j' (by omega)

theorem exp_fix_zero (W : GeneralModel.Weights) :
    GeneralModel.expFix W 0 = 1073741824 := by
  simp [GeneralModel.expFix, GeneralModel.EXP_ONE]

theorem list_foldl_add_sum : ∀ (l : List Int) (acc : Int),
    l.foldl Int.add acc = acc + l.sum
  | [], acc => by simp
  | x :: xs, acc => by
    have ih := list_foldl_add_sum xs (acc + x)
    have hsum : (x :: xs).sum = x + xs.sum := by simp
    show xs.foldl Int.add (acc + x) = acc + (x :: xs).sum
    rw [hsum]
    omega

theorem list_sum_nonneg : ∀ (l : List Int), (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.sum
  | [], _ => by simp
  | y :: ys, hnn => by
    have hy := hnn y (by simp)
    have hnn' : ∀ z ∈ ys, 0 ≤ z := fun z hz => hnn z (List.mem_cons_of_mem _ hz)
    have hys := list_sum_nonneg ys hnn'
    simp only [List.sum_cons]
    omega

theorem list_sum_bound : ∀ (l : List Int), (∀ x ∈ l, 0 ≤ x ∧ x ≤ 1073741824) →
    0 ≤ l.sum ∧ l.sum ≤ (l.length : Int) * 1073741824
  | [], _ => by simp
  | y :: ys, hb => by
    have hby := hb y (by simp)
    have hb' : ∀ x ∈ ys, 0 ≤ x ∧ x ≤ 1073741824 :=
      fun x hx => hb x (List.mem_cons_of_mem _ hx)
    have hys := list_sum_bound ys hb'
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one] at hys ⊢
    constructor <;> nlinarith

theorem list_sum_ge_mem : ∀ (l : List Int), (∀ x ∈ l, 0 ≤ x) →
    ∀ (x : Int), x ∈ l → x ≤ l.sum
  | [], _, _, hx => by simp at hx
  | y :: ys, hnn, x, hx => by
    have hnn' : ∀ z ∈ ys, 0 ≤ z := fun z hz => hnn z (List.mem_cons_of_mem _ hz)
    have hysum := list_sum_nonneg ys hnn'
    have hy := hnn y (by simp)
    simp only [List.sum_cons]
    by_cases hx1 : x = y
    · rw [hx1]
      omega
    · have hx' : x ∈ ys := by
        rcases List.mem_cons.mp hx with h1 | h1
        · exact absurd h1 hx1
        · exact h1
      have hys := list_sum_ge_mem ys hnn' x hx'
      omega

theorem take_all_len (l : List Int) (n : Nat) (h : l.length ≤ n) : l.take n = l := by
  induction l generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      have hl : (x :: xs).length = xs.length + 1 := by simp
      rw [hl] at h
      simpa using ih n (by omega)

/-- The joint bound of the rounded softmax weights: one shared denominator. -/
theorem tdiv_sum_le (es : List Int) (d : Int) (hd : 0 < d)
    (hnn : ∀ e ∈ es, 0 ≤ e) (hsum : es.sum = d) :
    (es.map (fun e => (e * 16777216).tdiv d)).sum ≤ 16777216 := by
  have key : ∀ (l : List Int), (∀ e ∈ l, 0 ≤ e) →
      ((l.map (fun e => (e * 16777216).tdiv d)).sum * d ≤ 16777216 * l.sum) := by
    intro l hl
    induction l with
    | nil => simp
    | cons e l ih =>
      have hnnl : ∀ e ∈ l, 0 ≤ e := fun x hx => hl x (List.mem_cons_of_mem _ hx)
      have hih := ih hnnl
      have he := hl e (by simp)
      have hmul : (e * 16777216).tdiv d * d ≤ e * 16777216 := by
        have hpos : 0 ≤ e * 16777216 := by omega
        have hed : (e * 16777216).tdiv d = (e * 16777216) / d :=
          Int.tdiv_eq_ediv_of_nonneg hpos
        rw [hed]
        exact Int.ediv_mul_le _ (by omega)
      simp only [List.map_cons, List.sum_cons] at hih ⊢
      nlinarith
  have hkey := key es hnn
  rw [hsum] at hkey
  nlinarith

/-- Total correctness of the running-maximum loop, with the score envelope. -/
theorem softmax_max_loop_spec (s : Array I64 32#usize) (p : Usize)
    (m : I64) (hm : m.val = GeneralModel.nth 0 (ints s) 0)
    (hp : p.val < 32) (hs : Bounded Envelope.score s) :
    general_engine.softmax_at_loop0 s p m 1#usize ⦃ r =>
      r.val = softMaxScan (ints s) (p.val + 1) ∧
      -930186526720 ≤ r.val ∧ r.val ≤ 930186526720 ⦄ := by
  unfold general_engine.softmax_at_loop0
  apply loop.spec_decr_nat
    (measure := fun st : I64 × Usize => p.val + 1 - st.2.val)
    (inv := fun st : I64 × Usize =>
      st.2.val ≤ p.val + 1 ∧ st.1.val = softMaxScan (ints s) st.2.val ∧
      -930186526720 ≤ st.1.val ∧ st.1.val ≤ 930186526720)
  · rintro ⟨smax, j⟩ ⟨hj, hsm, hslo, hshi⟩
    unfold general_engine.softmax_at_loop0.body
    dsimp only at hj hsm hslo hshi ⊢
    split
    · have hjp : j.val ≤ p.val := by scalar_tac
      have hj32 : j.val < 32 := by omega
      step as ⟨i, hi⟩
      have hnth : GeneralModel.nth 0 (ints s) j.val =
          (ints s)[j.val]'(by rw [ints_length32]; exact hj32) :=
        project_nth_eq _ _ _ (by rw [ints_length32]; exact hj32)
      have hie : i.val = GeneralModel.nth 0 (ints s) j.val := by
        rw [hnth]
        simp [ints, hi]
      have hib : -930186526720 ≤ i.val ∧ i.val ≤ 930186526720 := by
        have hl : s.val.length = 32 := by simp
        have hmem : i ∈ s.val := by rw [hi]; exact List.getElem_mem (by omega)
        exact hs i hmem
      split
      · have hgt : i.val > smax.val := by scalar_tac
        step as ⟨j1, hj1⟩
        have hj1v : j1.val = j.val + 1 := by scalar_tac
        refine ⟨by omega, ?_, ?_, by omega⟩
        · rw [hj1v, soft_max_scan_succ, if_pos (by omega)]
          exact hie
        · omega
      · have hle : ¬ i.val > smax.val := by scalar_tac
        step as ⟨j1, hj1⟩
        have hj1v : j1.val = j.val + 1 := by scalar_tac
        refine ⟨by omega, ?_, ?_, by omega⟩
        · rw [hj1v, soft_max_scan_succ, if_neg (by omega)]
          exact hsm
        · omega
    · have hjp : j.val = p.val + 1 := by scalar_tac
      simp only [WP.spec_ok]
      rw [← hjp]
      exact ⟨hsm, hslo, hshi⟩
  · have hl : s.val.length = 32 := by simp
    have hpos : 0 < s.val.length := by omega
    have hnth : GeneralModel.nth 0 (ints s) 0 =
        (ints s)[0]'(by rw [ints_length32]; omega) :=
      project_nth_eq _ _ _ (by rw [ints_length32]; omega)
    have hint : (ints s)[0]'(by rw [ints_length32]; omega) = (s.val[0]'(hpos)).val := by
      have hge : s.val[0]! = s.val[0]'(hpos) := getElem!_pos s.val 0 hpos
      have h1 : (ints s)[0]'(by rw [ints_length32]; omega) = (s.val[0]!).val :=
        getElem_ints s 0 (by omega)
      rw [h1, ← hge]
    have hmem : s.val[0]'(hpos) ∈ s.val := List.getElem_mem hpos
    have hb := hs _ hmem
    have hm0 : -930186526720 ≤ m.val ∧ m.val ≤ 930186526720 := by
      rw [hm, hnth, hint]
      exact hb
    refine ⟨by scalar_tac, ?_, hm0.1, hm0.2⟩
    show m.val = softMaxScan (ints s) 1
    rw [hm, soft_max_scan_one]

/-- Pointwise entries of the exponential scan, with the running denominator. -/
theorem softmax_exp_loop_spec (W : general_engine.Weights) (hW : LoadBounds W)
    (s : Array I64 32#usize) (p : Usize) (hp : p.val < 32)
    (hs : Bounded Envelope.score s)
    (smax : I64) (hsmax : smax.val = softMaxScan (ints s) (p.val + 1))
    (hsmaxb : -930186526720 ≤ smax.val ∧ smax.val ≤ 930186526720) :
    general_engine.softmax_at_loop1 W s p smax 0#usize
      (Array.repeat 32#usize 0#i64) 0#i64 ⦃ r =>
      (∀ (j : Nat) (hj : j < p.val + 1), (ints r.1)[j]'(by rw [ints_length32]; omega) =
        softEsAt (toGeneralModel W) (ints s) smax.val j) ∧
      r.2.val = (softEs (toGeneralModel W) (ints s) smax.val p.val).sum ∧
      (∀ v ∈ r.1.val, 0 ≤ v.val ∧ v.val ≤ 1073741824) ⦄ := by
  unfold general_engine.softmax_at_loop1
  apply loop.spec_decr_nat
    (measure := fun st : Usize × (Array I64 32#usize) × I64 => p.val + 1 - st.1.val)
    (inv := fun st : Usize × (Array I64 32#usize) × I64 =>
      st.1.val ≤ p.val + 1 ∧
      (∀ (j : Nat) (hj : j < st.1.val) (hj32 : j < 32),
        (ints st.2.1)[j]'(by rw [ints_length32]; omega) =
        softEsAt (toGeneralModel W) (ints s) smax.val j) ∧
      (∀ v ∈ st.2.1.val, 0 ≤ v.val ∧ v.val ≤ 1073741824) ∧
      st.2.2.val = ((softEs (toGeneralModel W) (ints s) smax.val p.val).take st.1.val).sum ∧
      0 ≤ st.2.2.val ∧ st.2.2.val ≤ (st.1.val : Int) * 1073741824)
  · rintro ⟨j, e, den⟩ ⟨hj, hpt, hbd, hden, hdenlo, hdenhi⟩
    unfold general_engine.softmax_at_loop1.body
    dsimp only at hj hpt hbd hden hdenlo hdenhi ⊢
    split
    · have hjp : j.val ≤ p.val := by scalar_tac
      have hj32 : j.val < 32 := by omega
      step as ⟨i, hi⟩
      have hnth : GeneralModel.nth 0 (ints s) j.val =
          (ints s)[j.val]'(by rw [ints_length32]; exact hj32) :=
        project_nth_eq _ _ _ (by rw [ints_length32]; exact hj32)
      have hie : i.val = GeneralModel.nth 0 (ints s) j.val := by
        rw [hnth]
        simp [ints, hi]
      have hib : -930186526720 ≤ i.val ∧ i.val ≤ 930186526720 := by
        have hl : s.val.length = 32 := by simp
        have hmem : i ∈ s.val := by rw [hi]; exact List.getElem_mem (by omega)
        exact hs i hmem
      step as ⟨d, hd⟩
      have hdv : d.val = smax.val - GeneralModel.nth 0 (ints s) j.val := by
        rw [← hie]
        scalar_tac
      have hdpos : 0 ≤ d.val := by
        have hge := soft_max_scan_ge (ints s) (p.val + 1) j.val (by omega)
        rw [hdv, hsmax]
        omega
      step with exp_spec W hW d hdpos as ⟨v, hv, hvlo, hvhi⟩
      have hvm : v.val = softEsAt (toGeneralModel W) (ints s) smax.val j := by
        rw [hv, hdv]
        rfl
      step as ⟨e1, he1⟩
      have hbde1 : ∀ v' ∈ e1.val, 0 ≤ v'.val ∧ v'.val ≤ 1073741824 := by
        intro v' hv'
        rw [he1] at hv'
        have h1 : v' ∈ e.val.set j.val v := Array.set_val_eq e j v ▸ hv'
        rcases List.mem_or_eq_of_mem_set h1 with h | h
        · exact hbd v' h
        · rw [h]
          exact ⟨hvlo, hvhi⟩
      step as ⟨i3, hi3⟩
      have hi3v : i3 = v := by
        rw [hi3]
        simp only [he1, Array.set_val_eq, List.getElem_set_self]
      step as ⟨den1, hden1⟩
      step as ⟨j1, hj1⟩
      have hj1v : j1.val = j.val + 1 := by scalar_tac
      have hden1v : den1.val = den.val + v.val := by
        rw [← hi3v]
        scalar_tac
      have hget : ((softEs (toGeneralModel W) (ints s) smax.val p.val))[j.val]? =
          some (softEsAt (toGeneralModel W) (ints s) smax.val j) := by
        simp only [softEs, List.getElem?_map,
          List.getElem?_range (show j.val < p.val + 1 by omega)]
        rfl
      have htake : ((softEs (toGeneralModel W) (ints s) smax.val p.val).take (j.val + 1)).sum =
          ((softEs (toGeneralModel W) (ints s) smax.val p.val).take j.val).sum +
            softEsAt (toGeneralModel W) (ints s) smax.val j := by
        rw [List.take_add_one, hget, Option.toList_some]
        simp only [List.sum_append, List.sum_cons, List.sum_nil, Int.add_zero]
      have hden1b : 0 ≤ den1.val ∧ den1.val ≤ 34359738368 := by
        have hden1v : den1.val = den.val + i3.val := by scalar_tac
        have hi3vv : i3.val = v.val := by rw [hi3v]
        omega
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, by omega⟩
      · intro j' hj' hj32
        by_cases hjj : j' < j.val
        · have hval : (ints e1)[j']'(by rw [ints_length32]; omega) =
              (ints e)[j']'(by rw [ints_length32]; omega) := by
            simp only [he1, ints, Array.set_val_eq, List.getElem_map]
            rw [List.getElem_set_ne (by omega)]
          rw [← hpt j' hjj (by omega)]
          exact hval
        · have hje : j' = j.val := by omega
          subst j'
          have hval : (ints e1)[j.val]'(by rw [ints_length32]; omega) = v.val := by
            simp [he1, Array.set_val_eq, List.getElem_set_self, ints, List.getElem_map]
          rw [← hvm]
          exact hval
      · exact hbde1
      · rw [hj1v]
        omega
      · omega
      · omega
    · have hjp : j.val = p.val + 1 := by scalar_tac
      simp only [WP.spec_ok, hjp]
      refine ⟨?_, ?_, hbd⟩
      · intro j' hj'
        exact hpt j' (by omega) (by omega)
      · have htake : (softEs (toGeneralModel W) (ints s) smax.val p.val).take (p.val + 1) =
          softEs (toGeneralModel W) (ints s) smax.val p.val :=
          take_all_len _ _ (softEs_length _ _ _ _).le
        rw [hjp, htake] at hden
        exact hden
  · refine ⟨by scalar_tac, ?_, ?_, ?_, ?_, ?_⟩
    · intro j' hj' hj32
      exact absurd hj' (by show ¬(j' < 0); omega)
    · intro v hv
      have : v = 0#i64 := by simpa using hv
      subst v
      constructor <;> scalar_tac
    · simp
    · scalar_tac
    · scalar_tac

/-- Pointwise rounded weights of the division loop. -/
theorem softmax_div_loop_spec (p : Usize) (hp : p.val < 32)
    (e : Array I64 32#usize) (den : I64) (hd : 0 < den.val)
    (henn : ∀ v ∈ e.val, 0 ≤ v.val ∧ v.val ≤ 1073741824) :
    general_engine.softmax_at_loop2 p 0#usize e den (Array.repeat 32#usize 0#i64) ⦃ r =>
      (∀ (j : Nat) (hj : j < p.val + 1), (ints r)[j]'(by rw [ints_length32]; omega) =
        ((ints e)[j]'(by rw [ints_length32]; omega) * 16777216).tdiv den.val) ∧
      (∀ v ∈ r.val, 0 ≤ v.val) ⦄ := by
  have halpha : general_engine.ALPHA_ONE = ok 16777216#i64 := by
    unfold general_engine.ALPHA_ONE; rfl
  unfold general_engine.softmax_at_loop2
  apply loop.spec_decr_nat
    (measure := fun st : Usize × (Array I64 32#usize) => p.val + 1 - st.1.val)
    (inv := fun st : Usize × (Array I64 32#usize) =>
      st.1.val ≤ p.val + 1 ∧
      (∀ (j : Nat) (hj : j < st.1.val) (hj32 : j < 32),
        (ints st.2)[j]'(by rw [ints_length32]; omega) =
        ((ints e)[j]'(by rw [ints_length32]; omega) * 16777216).tdiv den.val) ∧
      (∀ v ∈ st.2.val, 0 ≤ v.val))
  · rintro ⟨j, alpha⟩ ⟨hj, hpt, hbd⟩
    unfold general_engine.softmax_at_loop2.body
    dsimp only at hj hpt hbd ⊢
    rw [halpha]
    split
    · have hjp : j.val ≤ p.val := by scalar_tac
      have hj32 : j.val < 32 := by omega
      step as ⟨i, hi⟩
      have hiv : i.val = (ints e)[j.val]'(by rw [ints_length32]; exact hj32) := by
        simp [ints, hi]
      have hib : 0 ≤ i.val ∧ i.val ≤ 1073741824 := by
        have hl : e.val.length = 32 := by simp
        have hmem : i ∈ e.val := by rw [hi]; exact List.getElem_mem (by omega)
        exact henn i hmem
      step as ⟨m, hm⟩
      step as ⟨q, hq⟩
      step as ⟨alph, halph⟩
      step as ⟨j1, hj1⟩
      have hqv : q.val = ((ints e)[j.val]'(by rw [ints_length32]; exact hj32) * 16777216).tdiv den.val := by
        rw [hq, hm, hiv]
      have hqnn : 0 ≤ q.val := by
        rw [hqv]
        exact Int.tdiv_nonneg (by omega) (by omega)
      have hj1v : j1.val = j.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, ?_, by omega⟩
      · intro j' hj' hj32
        by_cases hjj : j' < j.val
        · have hval : (ints alph)[j']'(by rw [ints_length32]; omega) =
              (ints alpha)[j']'(by rw [ints_length32]; omega) := by
            simp only [halph, ints, Array.set_val_eq, List.getElem_map]
            rw [List.getElem_set_ne (by omega)]
          rw [← hpt j' hjj (by omega)]
          exact hval
        · have hje : j' = j.val := by omega
          subst j'
          have hval : (ints alph)[j.val]'(by rw [ints_length32]; omega) = q.val := by
            simp [halph, Array.set_val_eq, List.getElem_set_self, ints, List.getElem_map]
          rw [hval]
          exact hqv
      · intro v' hv'
        by_cases hvj : v' = q
        · subst v'
          exact hqnn
        · have hmem : v' ∈ alpha.val := by
            rw [halph, Array.set_val_eq alpha j q] at hv'
            rcases List.mem_or_eq_of_mem_set hv' with h | h
            · exact h
            · exact absurd h (by simpa using hvj)
          exact hbd v' hmem
    · have hjp : j.val = p.val + 1 := by scalar_tac
      simp only [WP.spec_ok, hjp]
      exact ⟨fun j' hj' => hpt j' (by omega) (by omega), hbd⟩
  · refine ⟨by scalar_tac, ?_, ?_⟩
    · intro j' hj' hj32
      exact absurd hj' (by show ¬(j' < 0); omega)
    · intro v hv
      have : v = 0#i64 := by simpa using hv
      subst v
      scalar_tac

/-- The complete causal softmax: exact model equality, nonnegative weights and the joint
sum bound. -/
theorem softmax_at_spec (W : general_engine.Weights) (hW : LoadBounds W)
    (s : Array I64 32#usize) (p : Usize) (hp : p.val < 32)
    (hs : Bounded Envelope.score s) :
    general_engine.softmax_at W s p ⦃ r =>
      (ints r).take (p.val + 1) = GeneralModel.softmaxAt (toGeneralModel W) (ints s) p.val ∧
      (∀ v ∈ r.val, 0 ≤ v.val) ∧
      ((ints r).take (p.val + 1)).sum ≤ 16777216 ⦄ := by
  unfold general_engine.softmax_at
  step as ⟨s0, hs0⟩
  have hs0v : s0.val = GeneralModel.nth 0 (ints s) 0 := by
    have hnth : GeneralModel.nth 0 (ints s) 0 =
        (ints s)[0]'(by rw [ints_length32]; omega) :=
      project_nth_eq _ _ _ (by rw [ints_length32]; omega)
    have h3 : s0.val = (ints s)[0]'(by rw [ints_length32]; omega) := by
      rw [hs0]
      simp [ints]
    omega
  step with softmax_max_loop_spec s p s0 hs0v hp hs
    as ⟨smax, hsmaxm, hsmaxlo, hsmaxhi⟩
  have hsmax : smax.val = softMaxScan (ints s) (p.val + 1) := hsmaxm
  step with softmax_exp_loop_spec W hW s p hp hs smax hsmax ⟨hsmaxlo, hsmaxhi⟩
    as ⟨e, den, hpt, hden, hbd⟩
  have hsum : (softEs (toGeneralModel W) (ints s) smax.val p.val).sum = den.val := hden.symm
  have hle : (softEs (toGeneralModel W) (ints s) smax.val p.val).length = p.val + 1 :=
    softEs_length _ _ _ _
  have hnn : ∀ x ∈ softEs (toGeneralModel W) (ints s) smax.val p.val, 0 ≤ x := by
    intro x hx
    obtain ⟨j', hj', rfl⟩ := List.mem_iff_getElem.mp hx
    have hjp' : j' < p.val + 1 := by omega
    have hev : (ints e)[j']'(by rw [ints_length32]; omega) =
        softEsAt (toGeneralModel W) (ints s) smax.val j' := hpt j' hjp'
    have hv : 0 ≤ (ints e)[j']'(by rw [ints_length32]; omega) := by
      have hl : e.val.length = 32 := by simp
      have hem : e.val[j']'(by omega) ∈ e.val := List.getElem_mem (by omega)
      have hb := hbd _ hem
      simpa [ints] using hb.1
    have hval' : (softEs (toGeneralModel W) (ints s) smax.val p.val)[j']'hj' =
        softEsAt (toGeneralModel W) (ints s) smax.val j' :=
      softEs_getElem _ _ _ _ _ hjp'
    rw [hval', ← hev]
    exact hv
  have hdenpos : 0 < den.val := by
    obtain ⟨j0, hj0, hje⟩ := soft_max_scan_attained (ints s) (p.val + 1) (by omega)
    have hentry : softEsAt (toGeneralModel W) (ints s) smax.val j0 = 1073741824 := by
      rw [softEsAt, hje, ← hsmax]
      rw [show smax.val - smax.val = 0 from Int.sub_self _]
      exact exp_fix_zero _
    have hj0le : j0 < (softEs (toGeneralModel W) (ints s) smax.val p.val).length := by
      rw [hle]; omega
    have hval0 : (softEs (toGeneralModel W) (ints s) smax.val p.val)[j0]'hj0le =
        softEsAt (toGeneralModel W) (ints s) smax.val j0 :=
      softEs_getElem _ _ _ _ _ (by omega)
    have hmem : 1073741824 ∈ softEs (toGeneralModel W) (ints s) smax.val p.val :=
      List.mem_iff_getElem.mpr ⟨j0, hj0le, by rw [hval0]; exact hentry⟩
    have hsumge := list_sum_ge_mem _ hnn _ hmem
    omega
  step with softmax_div_loop_spec p hp e den hdenpos hbd as ⟨alpha, halpha', halnn⟩
  have htakelist : (ints alpha).take (p.val + 1) =
      (softEs (toGeneralModel W) (ints s) smax.val p.val).map
        (fun e' => (e' * 16777216).tdiv den.val) := by
    have hla : (ints alpha).length = 32 := ints_length32 alpha
    apply List.ext_getElem
    · simp only [List.length_take, List.length_map]
      omega
    · intro j hj hj'
      simp only [List.length_map] at hj'
      have hjp : j < p.val + 1 := by omega
      have htake : ((ints alpha).take (p.val + 1))[j]'(by omega) =
          (ints alpha)[j]'(by rw [ints_length32]; omega) :=
        (List.getElem_take' (by rw [ints_length32]; omega) (by omega)).symm
      rw [htake, halpha' j hjp]
      have hej : (ints e)[j]'(by rw [ints_length32]; omega) =
          softEsAt (toGeneralModel W) (ints s) smax.val j := hpt j hjp
      rw [hej, List.getElem_map, softEs_getElem _ _ _ _ _ hjp]
  refine ⟨?_, halnn, ?_⟩
  · have hmodel : GeneralModel.softmaxAt (toGeneralModel W) (ints s) p.val =
        (softEs (toGeneralModel W) (ints s) smax.val p.val).map
          (fun e' => (e' * 16777216).tdiv den.val) := by
      have hsm : GeneralModel.softmaxMax (ints s) p.val = smax.val := by
        have h0 : GeneralModel.softmaxMax (ints s) p.val = softMaxScan (ints s) (p.val + 1) := rfl
        omega
      have h1 : softEs (toGeneralModel W) (ints s) smax.val p.val =
          List.map
            (fun j => GeneralModel.expFix (toGeneralModel W)
              (Int.sub smax.val (GeneralModel.nth 0 (ints s) j)))
            (List.range (p.val + 1)) := rfl
      have hf : (List.map
          (fun j => GeneralModel.expFix (toGeneralModel W)
            (Int.sub smax.val (GeneralModel.nth 0 (ints s) j)))
          (List.range (p.val + 1))).foldl Int.add (Int.ofNat 0) = den.val := by
        rw [← h1]
        have h3 := list_foldl_add_sum (softEs (toGeneralModel W) (ints s) smax.val p.val)
          (Int.ofNat 0)
        have h3' : (softEs (toGeneralModel W) (ints s) smax.val p.val).foldl Int.add
            (Int.ofNat 0) = 0 + (softEs (toGeneralModel W) (ints s) smax.val p.val).sum := h3
        omega
      simp only [GeneralModel.softmaxAt, hsm, GeneralModel.ALPHA_ONE, hf]
      rfl
    rw [htakelist, hmodel]
  · rw [htakelist]
    exact tdiv_sum_le _ _ hdenpos hnn hsum

end LcnExec.GeneralEngine
