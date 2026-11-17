import TransformerInt.Model

/-!
# A packed evaluator for the kernel, proved to give the model's answer

Lean's kernel spends about the same time on each small arithmetic step, and `forward` in
`Model.lean` has 277,376 multiply-adds per input pair. This file computes the same logits with
fewer steps, in two ways.

**Tables.** The attention scores and the value vectors depend on the head, the position and the
token only, not on the pair. `Tables` holds them: 908 scores and 908 value vectors. `TablesOk`
states that every entry equals the model's own expression for it; the generated `TablesOk.lean`
proves that by evaluating the model in the kernel, once.

**Packing.** A matrix product `lincomb n x w` is evaluated as in lean-checked-network's
`Fast.lean`: each row of `w` is packed into one integer, entry `i` at the digit `B^i` (`pkI`).
Packing is linear, so `sum over k of x[k] * pkI w[k]` is the packed result: one multiplication of
a large number per row instead of one per entry. The entries are signed, so before the digits are
read back `K = 2^61` is added to every digit, and `K` is subtracted from each digit read (`unpk`).
This is exact when every entry of the result lies in `[-K, K]`, which `flc` checks from the size
of `x` and a bound on the entries of `w`, and refuses otherwise.

**The base is odd on purpose.** The kernel caches every term it reduces in a hash table, and the
hash of a number literal is its low 32 bits. With a base `2^64` (or any multiple of `2^32`) every
product `B * n` has the same hash, the cache degenerates into a few long chains, and the time per
step grows with the number of steps: packing 14,464 entries took 28.5 s at `B = 2^64` and 2.47 s
at the odd base below (measured 2026-11-17, Lean v4.35.0). `B = 2^63 + 0x9E3779B1`.

**Packed rows are literals.** The generated `Packed.lean` holds `pkRows` of the four large
matrices as numbers, and `Static.lean` proves them equal to `pkRows` of the weights, once. A row
module then starts from the packed numbers and does not pack anything.

`fastPredict_sound` proves: if the packed evaluator returns an answer, the model returns the same
answer. Nothing here is trusted beyond Lean's kernel.
-/

namespace TransformerInt

/-! ## `Int.add`, `Int.mul`, `Int.sub` are `+`, `*`, `-` -/

theorem iadd (a b : Int) : Int.add a b = a + b := rfl
theorem imul (a b : Int) : Int.mul a b = a * b := rfl

/-! ## Packing -/

/-- The base of the packed representation, `2^63 + 0x9E3779B1`: odd, see the note above. -/
def B : Nat := 9223372039509211569

/-- The shift added to every digit, 2^61. Packed entries must lie in `[-K, K]`, and `2 * K < B`. -/
def K : Nat := 2305843009213693952

/-- Signed digits `[d0, d1, ...]` packed as `d0 + B * (d1 + B * (...))`. -/
def pkI : List Int → Int
  | [] => .ofNat 0
  | d :: ds => Int.add d (Int.mul (.ofNat B) (pkI ds))

/-- Every row packed. -/
def pkRows : List (List Int) → List Int
  | [] => []
  | r :: rs => pkI r :: pkRows rs

/-- `n` digits 1, packed: `1 + B + ... + B^(n-1)`. -/
def ones : Nat → Nat
  | 0 => 0
  | n + 1 => 1 + B * ones n

/-- The first `n` base-`B` digits of `N`, each with `K` subtracted. -/
def unpk : Nat → Nat → List Int
  | 0, _ => []
  | n + 1, N => Int.subNatNat (N % B) K :: unpk n (N / B)

/-- The sum of the absolute values. -/
def sumAbs : List Int → Nat
  | [] => 0
  | x :: xs => Int.natAbs x + sumAbs xs

/-- `lincomb n x w`, computed on the packed rows `p = pkRows w`. `m` bounds the absolute entries
of `w` (`rowsOk`). Returns `none` when `m * sumAbs x` exceeds `K`, in which case a digit could
leave its window. -/
def flc (n m : Nat) (x : List Int) (p : List Int) : Option (List Int) :=
  if m * sumAbs x ≤ K then
    some (unpk n (Int.toNat (Int.add (dot x p) (.ofNat (K * ones n)))))
  else none

/-- Every entry has absolute value at most `m`. -/
def bddB (m : Nat) : List Int → Bool
  | [] => true
  | e :: es => Nat.ble (Int.natAbs e) m && bddB m es

/-- Every row has `n` entries, each of absolute value at most `m`. -/
def rowsOk (n m : Nat) : List (List Int) → Bool
  | [] => true
  | r :: rs => (Nat.beq r.length n && bddB m r) && rowsOk n m rs

/-! ## Why the packed product is the product -/

/-- Every entry has absolute value at most `m`. -/
def Bdd (m : Nat) : List Int → Prop
  | [] => True
  | e :: es => Int.natAbs e ≤ m ∧ Bdd m es

/-- Every row has `n` entries, each of absolute value at most `m`. -/
def RowsBdd (n m : Nat) : List (List Int) → Prop
  | [] => True
  | r :: rs => (r.length = n ∧ Bdd m r) ∧ RowsBdd n m rs

theorem bdd_of_bddB (m : Nat) : ∀ v : List Int, bddB m v = true → Bdd m v
  | [], _ => trivial
  | e :: es, h => by
    simp only [bddB, Bool.and_eq_true, Nat.ble_eq] at h
    exact ⟨h.1, bdd_of_bddB m es h.2⟩

theorem rowsBdd_of_rowsOk (n m : Nat) : ∀ w : List (List Int), rowsOk n m w = true → RowsBdd n m w
  | [], _ => trivial
  | r :: rs, h => by
    simp only [rowsOk, Bool.and_eq_true] at h
    exact ⟨⟨Nat.eq_of_beq_eq_true h.1.1, bdd_of_bddB m r h.1.2⟩, rowsBdd_of_rowsOk n m rs h.2⟩

theorem bdd_mono {m m' : Nat} (h : m ≤ m') : ∀ v : List Int, Bdd m v → Bdd m' v
  | [], _ => trivial
  | _ :: es, hv => ⟨Nat.le_trans hv.1 h, bdd_mono h es hv.2⟩

theorem bdd_replicate (m n : Nat) : Bdd m (List.replicate n (Int.ofNat 0)) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨Nat.zero_le _, ih⟩

theorem bdd_scale (c : Int) (m : Nat) : ∀ r : List Int, Bdd m r → Bdd (Int.natAbs c * m) (scale c r)
  | [], _ => trivial
  | e :: es, h => by
    refine ⟨?_, bdd_scale c m es h.2⟩
    rw [imul, Int.natAbs_mul]
    exact Nat.mul_le_mul_left _ h.1

theorem bdd_addV (p q : Nat) : ∀ u v : List Int, Bdd p u → Bdd q v → Bdd (p + q) (addV u v)
  | [], _, _, _ => trivial
  | _ :: _, [], _, _ => trivial
  | a :: u, b :: v, hu, hv => by
    refine ⟨?_, bdd_addV p q u v hu.2 hv.2⟩
    rw [iadd]
    have := Int.natAbs_add_le a b
    have := hu.1
    have := hv.1
    omega

theorem length_scale (c : Int) : ∀ r : List Int, (scale c r).length = r.length
  | [] => rfl
  | _ :: es => by simp only [scale, List.length_cons, length_scale c es]

theorem length_addV : ∀ u v : List Int, u.length = v.length → (addV u v).length = v.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | _ :: u, _ :: v, h => by
    simp only [addV, List.length_cons]
    rw [length_addV u v (by simpa using h)]

theorem pkI_scale (c : Int) : ∀ r : List Int, pkI (scale c r) = c * pkI r
  | [] => by show (0 : Int) = c * 0; omega
  | e :: es => by
    simp only [scale, pkI, iadd, imul, pkI_scale c es]
    rw [Int.mul_add, Int.mul_left_comm]

theorem pkI_addV : ∀ u v : List Int, u.length = v.length → pkI (addV u v) = pkI u + pkI v
  | [], [], _ => by show (0 : Int) = 0 + 0; omega
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: u, b :: v, h => by
    simp only [addV, pkI, iadd, imul, pkI_addV u v (by simpa using h)]
    rw [Int.mul_add]
    omega

theorem pkI_replicate : ∀ n : Nat, pkI (List.replicate n (Int.ofNat 0)) = 0
  | 0 => rfl
  | n + 1 => by
    simp only [List.replicate_succ, pkI, iadd, imul, pkI_replicate n]
    show (0 : Int) + _ * 0 = 0
    omega

/-- The model's product has `n` entries, bounded by `m * sumAbs x`, and its packing is the packed
product. -/
theorem lincomb_spec (n m : Nat) : ∀ (x : List Int) (w : List (List Int)), RowsBdd n m w →
    (lincomb n x w).length = n ∧ Bdd (m * sumAbs x) (lincomb n x w) ∧
      pkI (lincomb n x w) = dot x (pkRows w)
  | [], _, _ => ⟨List.length_replicate .., bdd_replicate _ n, pkI_replicate n⟩
  | _ :: _, [], _ => ⟨List.length_replicate .., bdd_replicate _ n, pkI_replicate n⟩
  | a :: xs, r :: rs, h => by
    obtain ⟨hlen, hbd, hpk⟩ := lincomb_spec n m xs rs h.2
    have hl : (scale a r).length = (lincomb n xs rs).length := by
      rw [length_scale, hlen, h.1.1]
    refine ⟨?_, ?_, ?_⟩
    · simp only [lincomb]
      rw [length_addV _ _ hl, hlen]
    · simp only [lincomb, sumAbs]
      rw [Nat.mul_add, Nat.mul_comm m (Int.natAbs a)]
      exact bdd_addV _ _ _ _ (bdd_scale a m r h.1.2) hbd
    · simp only [lincomb, pkRows, dot, iadd, imul]
      rw [pkI_addV _ _ hl, pkI_scale, hpk]

/-- The packing of entries in `[-K, K]`, shifted by `K` at every digit, is not negative. -/
theorem shifted_nonneg : ∀ v : List Int, Bdd K v →
    0 ≤ pkI v + ((K * ones v.length : Nat) : Int)
  | [], _ => by show (0 : Int) ≤ 0 + ((K * 0 : Nat) : Int); omega
  | d :: ds, h => by
    have ih := shifted_nonneg ds h.2
    have hd := h.1
    simp only [pkI, ones, List.length_cons, iadd, imul, Int.ofNat_eq_natCast] at ih ⊢
    generalize pkI ds = M at ih ⊢
    generalize ones ds.length = O at ih ⊢
    simp only [B, K] at ih hd ⊢
    omega

/-- Reading the shifted digits back gives the entries. -/
theorem unpk_pkI : ∀ v : List Int, Bdd K v →
    unpk v.length (Int.toNat (pkI v + ((K * ones v.length : Nat) : Int))) = v
  | [], _ => rfl
  | d :: ds, h => by
    have ih := unpk_pkI ds h.2
    have hM := shifted_nonneg ds h.2
    have hd := h.1
    simp only [pkI, ones, List.length_cons, unpk, iadd, imul, Int.ofNat_eq_natCast,
      Int.subNatNat_eq_coe] at ih hM ⊢
    generalize pkI ds = M at ih hM ⊢
    generalize ones ds.length = O at ih hM ⊢
    have key : ∀ N : Nat, N = (M + ((K * O : Nat) : Int)).toNat → unpk ds.length N = ds :=
      fun N e => e ▸ ih
    simp only [B, K] at hM hd key ⊢
    congr 1
    · omega
    · apply key
      omega

/-- The packed product is the model's product. -/
theorem flc_eq (n m : Nat) (x : List Int) (w : List (List Int)) (p v : List Int)
    (hw : rowsOk n m w = true) (hp : p = pkRows w) (h : flc n m x p = some v) :
    lincomb n x w = v := by
  obtain ⟨hlen, hbd, hpk⟩ := lincomb_spec n m x w (rowsBdd_of_rowsOk n m w hw)
  subst hp
  unfold flc at h
  split at h
  · rename_i hle
    injection h with h
    rw [← h, ← hpk, iadd, Int.ofNat_eq_natCast]
    have := unpk_pkI (lincomb n x w) (bdd_mono hle _ hbd)
    rw [hlen] at this
    exact this.symm
  · contradiction

/-! ## The evaluator -/

/-- What depends on the head, the position and the token only. `s0`, `s1`: the attention score
of each token at positions 0 and 1, per head; `s2`: the score of `=` at position 2, per head.
`v0`, `v1`, `v2`: the value vectors, in the same layout. -/
structure Tables where
  s0 : List (List Int)
  s1 : List (List Int)
  s2 : List Int
  v0 : List (List (List Int))
  v1 : List (List (List Int))
  v2 : List (List Int)

/-- Every table entry is the model's expression for it. -/
structure TablesOk (W : Weights) (T : Tables) : Prop where
  s0 : ∀ h, h < 4 → ∀ t, t < 113 →
    keyScore W h (embed W EQ 2) (embed W t 0) = nth 0 (nth [] T.s0 h) t
  s1 : ∀ h, h < 4 → ∀ t, t < 113 →
    keyScore W h (embed W EQ 2) (embed W t 1) = nth 0 (nth [] T.s1 h) t
  s2 : ∀ h, h < 4 → keyScore W h (embed W EQ 2) (embed W EQ 2) = nth 0 T.s2 h
  v0 : ∀ h, h < 4 → ∀ t, t < 113 → value W h (embed W t 0) = nth [] (nth [] T.v0 h) t
  v1 : ∀ h, h < 4 → ∀ t, t < 113 → value W h (embed W t 1) = nth [] (nth [] T.v1 h) t
  v2 : ∀ h, h < 4 → value W h (embed W EQ 2) = nth [] T.v2 h

/-- Bounds on the absolute entries of the matrices that are multiplied in packed form. -/
structure Bounds where
  wq : Nat
  wk : Nat
  wv : Nat
  wo : Nat
  win : Nat
  wout : Nat
  u : Nat

/-- The packed rows of the four matrices of the per-pair path: `wo` per head, `win`, `wout`, `u`. -/
structure Packed where
  wo : List (List Int)
  win : List Int
  wout : List Int
  u : List Int

/-- The matrices have the shapes and the entry bounds `flc` needs, and `Pk` holds their packed
rows. -/
structure StaticOk (W : Weights) (Bd : Bounds) (Pk : Packed) : Prop where
  wq : ∀ h, h < 4 → rowsOk 32 Bd.wq (nth [] W.wq h) = true
  wk : ∀ h, h < 4 → rowsOk 32 Bd.wk (nth [] W.wk h) = true
  wv : ∀ h, h < 4 → rowsOk 32 Bd.wv (nth [] W.wv h) = true
  wo : ∀ h, h < 4 → rowsOk 128 Bd.wo (nth [] W.wo h) = true
  win : rowsOk 512 Bd.win W.win = true
  wout : rowsOk 128 Bd.wout W.wout = true
  u : rowsOk 113 Bd.u W.u = true
  pwo : ∀ h, h < 4 → nth [] Pk.wo h = pkRows (nth [] W.wo h)
  pwin : Pk.win = pkRows W.win
  pwout : Pk.wout = pkRows W.wout
  pu : Pk.u = pkRows W.u

/-! ### The tables, through packed products -/

/-- `keyScore` with both projections packed. -/
def fastScore (W : Weights) (Bd : Bounds) (h : Nat) (x2 xj : List Int) : Option Int :=
  match flc 32 Bd.wq x2 (pkRows (nth [] W.wq h)), flc 32 Bd.wk xj (pkRows (nth [] W.wk h)) with
  | some q, some k => some (dot q k)
  | _, _ => none

/-- `value` with the projection packed. -/
def fastValue (W : Weights) (Bd : Bounds) (h : Nat) (xj : List Int) : Option (List Int) :=
  flc 32 Bd.wv xj (pkRows (nth [] W.wv h))

theorem fastScore_eq {W : Weights} {Bd : Bounds} {Pk : Packed} (hS : StaticOk W Bd Pk) (h : Nat)
    (hh : h < 4) (x2 xj : List Int) (s : Int) (e : fastScore W Bd h x2 xj = some s) :
    keyScore W h x2 xj = s := by
  unfold fastScore at e
  split at e
  · rename_i q k hq hk
    injection e with e
    unfold keyScore project
    rw [flc_eq _ _ _ _ _ _ (hS.wq h hh) rfl hq, flc_eq _ _ _ _ _ _ (hS.wk h hh) rfl hk]
    exact e
  · contradiction

theorem fastValue_eq {W : Weights} {Bd : Bounds} {Pk : Packed} (hS : StaticOk W Bd Pk) (h : Nat)
    (hh : h < 4) (xj v : List Int) (e : fastValue W Bd h xj = some v) : value W h xj = v :=
  flc_eq _ _ _ _ _ _ (hS.wv h hh) rfl e

/-! ### The per-pair path -/

/-- `headTerm` of the model for the pair `(a, b)`: scores and value vectors from the tables, the
product with `wo` packed. -/
def fastHead (W : Weights) (T : Tables) (Bd : Bounds) (Pk : Packed) (h a b : Nat) :
    Option (List Int) :=
  let alpha := softmaxWeights W (nth 0 (nth [] T.s0 h) a, nth 0 (nth [] T.s1 h) b, nth 0 T.s2 h)
  flc 128 Bd.wo
    (mix alpha.1 alpha.2.1 alpha.2.2 (nth [] (nth [] T.v0 h) a) (nth [] (nth [] T.v1 h) b)
      (nth [] T.v2 h))
    (nth [] Pk.wo h)

/-- `forward` of the model for the pair `(a, b)`, with the matrix products packed. -/
def fastForward (W : Weights) (T : Tables) (Bd : Bounds) (Pk : Packed) (a b : Nat) :
    Option (List Int) :=
  (fastHead W T Bd Pk 0 a b).bind fun w0 =>
  (fastHead W T Bd Pk 1 a b).bind fun w1 =>
  (fastHead W T Bd Pk 2 a b).bind fun w2 =>
  (fastHead W T Bd Pk 3 a b).bind fun w3 =>
  let r := residual (embed W EQ 2)
    (addV (addV (addV (addV (List.replicate 128 (.ofNat 0)) w0) w1) w2) w3)
  (flc 512 Bd.win r Pk.win).bind fun acc =>
  (flc 128 Bd.wout (hidden acc W.bin) Pk.wout).bind fun acc2 =>
  flc 113 Bd.u (finalStream r (addV acc2 W.bout)) Pk.u

/-- `predict` of the model for a pair in range, through `fastForward`. -/
def fastPredict (W : Weights) (T : Tables) (Bd : Bounds) (Pk : Packed) (a b : Nat) : Option Nat :=
  match fastForward W T Bd Pk a b with
  | some l => some (argmax l)
  | none => none

theorem fastHead_sound {W : Weights} {T : Tables} {Bd : Bounds} {Pk : Packed}
    (hS : StaticOk W Bd Pk) (hT : TablesOk W T) (h a b : Nat) (hh : h < 4) (ha : a < 113)
    (hb : b < 113) (w : List Int) (e : fastHead W T Bd Pk h a b = some w) :
    headTerm W h (embed W a 0) (embed W b 1) (embed W EQ 2) = w := by
  unfold headTerm headOutput headScores
  rw [hT.s0 h hh a ha, hT.s1 h hh b hb, hT.s2 h hh, hT.v0 h hh a ha, hT.v1 h hh b hb, hT.v2 h hh]
  exact flc_eq _ _ _ _ _ _ (hS.wo h hh) (hS.pwo h hh) e

theorem fastForward_sound {W : Weights} {T : Tables} {Bd : Bounds} {Pk : Packed}
    (hS : StaticOk W Bd Pk) (hT : TablesOk W T) (a b : Nat) (ha : a < 113) (hb : b < 113)
    (l : List Int) (e : fastForward W T Bd Pk a b = some l) : forward W a b = l := by
  unfold fastForward at e
  simp only [Option.bind_eq_some_iff] at e
  obtain ⟨w0, e0, w1, e1, w2, e2, w3, e3, acc, e4, acc2, e5, e6⟩ := e
  have h0 := fastHead_sound hS hT 0 a b (by decide) ha hb w0 e0
  have h1 := fastHead_sound hS hT 1 a b (by decide) ha hb w1 e1
  have h2 := fastHead_sound hS hT 2 a b (by decide) ha hb w2 e2
  have h3 := fastHead_sound hS hT 3 a b (by decide) ha hb w3 e3
  have h4 := flc_eq _ _ _ _ _ _ hS.win hS.pwin e4
  have h5 := flc_eq _ _ _ _ _ _ hS.wout hS.pwout e5
  have h6 := flc_eq _ _ _ _ _ _ hS.u hS.pu e6
  unfold forward attention mlpOutput mlpHidden unembed
  simp only [h0, h1, h2, h3, h4, h5, h6]

/-- If the packed evaluator returns an answer for a pair in range, the model returns it too. -/
theorem fastPredict_sound {W : Weights} {T : Tables} {Bd : Bounds} {Pk : Packed}
    (hS : StaticOk W Bd Pk) (hT : TablesOk W T) (a b : Nat) (ha : a < 113) (hb : b < 113)
    (c : Nat) (e : fastPredict W T Bd Pk a b = some c) : predict W a b = some c := by
  unfold fastPredict at e
  split at e
  · rename_i l hl
    have hf := fastForward_sound hS hT a b ha hb l hl
    have hn : ¬(a ≥ P ∨ b ≥ P) := by simp only [P]; omega
    unfold predict
    simp only [hn, ↓reduceIte, hf]
    exact e
  · contradiction

end TransformerInt
