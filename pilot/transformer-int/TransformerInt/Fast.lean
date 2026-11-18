import TransformerInt.Model

/-!
# A packed evaluator for the kernel, proved to give the model's answer

Lean's kernel takes about as long for a multiply-add of two small numbers as for a multiply-add
of a small number and one of 2,400 digits (measured 2026-11-17, Lean v4.35.0: about 0.23 ms either
way, with the definitions of `Model.lean`), and `forward` has 277,376 multiply-adds per input
pair. This file computes the same logits in fewer steps. `fastPredict_sound` proves: if the
evaluator returns an answer for a pair in range, the model returns the same answer. Nothing here
is trusted beyond Lean's kernel.

**Tables.** The attention scores and the value vectors depend on the head, the position and the
token only, not on the pair. `Tables` holds them: 908 scores and 908 value vectors. `TablesOk`
states that every entry equals the model's own expression for it; the generated `TabOk*.lean`
prove that once, through `fastScore` and `fastValue`.

**Packing.** A matrix product `lincomb n x w` is evaluated as in lean-checked-network's
`Fast.lean`: each row of `w` is packed into one integer, entry `i` at the digit `B^i` (`pkI`).
Packing is linear, so `sum over k of x[k] * pkI w[k]` is the packed result: one multiplication of
a large number per row instead of one per entry. The entries are signed, so before the digits are
read back `K = 2^61` is added to every digit, and `K` is subtracted from each digit read (`unpk`).
This is exact when every entry of the result lies in `[-K, K]`, which `flc` checks from the size
of `x` and a bound on the entries of `w`, and refuses otherwise (`flc_eq`).

**The base is odd on purpose.** The kernel keeps the terms it has reduced in hash tables, and the
hash of a number literal depends only on its low 64 bits (`Hashable Nat` is `UInt64.ofNat`; Lean
v4.35.0 sources, read 2026-11-17). At the base `2^64` every product `B * n` has the same hash,
and the time per step grew with the number of steps: packing 14,464 entries in the kernel took
28.5 s at `B = 2^64` and 2.47 s at the odd base below (measured 2026-11-17, Lean v4.35.0; four of
four stack samples of a slow run were in the kernel's term comparison under a cache lookup).
`B = 2^63 + 0x9E3779B1`.

**Packed rows are literals.** The generated `PackedData.lean` holds `pkRows` of the four large
matrices and the packed bias as numbers, and `Static.lean` proves them equal to the packing of the
weights, once (`StaticOk`). A row module starts from the packed numbers and packs no row.

**Per pair** (`fastForward`): the four heads' products with `wo` are added while packed and read
back once (`fastAttn`); the hidden layer adds its bias while packed and applies ReLU and the
shift on natural numbers while reading the digits (`flcRelu`, `reluU`); the MLP output and the
unembedding are one `flc` each. The loops are recursor terms (see below).
-/

namespace TransformerInt

/-! ## `Int.add` and `Int.mul` are `+` and `*` -/

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

/-! ## The same loops as recursor terms

A definition by pattern matching reaches the kernel as a `brecOn` term, and the kernel spends two
to three times as long on one step of it as on one step of the recursor written out (measured
2026-11-17, Lean v4.35.0, on a list of 512: `dot` 119 ms and `dotR` 56 ms; `sumAbs` 23.8 ms and
`sumAbsR` 11 ms; `nth` at index 255, 11.7 ms and `nthR` 4.3 ms). The loops the kernel runs for
every pair are therefore written a second time as recursor terms, each proved equal to the
definition it stands for. They are `noncomputable`: only the kernel reduces them. -/

noncomputable section

/-- `nth`, as a recursor term. -/
def nthR {α : Type} (d : α) (l : List α) (n : Nat) : α :=
  @List.rec α (fun _ => Nat → α) (fun _ => d)
    (fun x _ ih n => @Nat.casesOn (fun _ => α) n x (fun m => ih m)) l n

/-- `dot`, as a recursor term. -/
def dotR (xs ys : List Int) : Int :=
  @List.rec Int (fun _ => List Int → Int) (fun _ => Int.ofNat 0)
    (fun x _ ih ys => @List.casesOn Int (fun _ => Int) ys (Int.ofNat 0)
      (fun y ys => Int.add (Int.mul x y) (ih ys))) xs ys

/-- `sumAbs`, as a recursor term. -/
def sumAbsR (xs : List Int) : Nat :=
  @List.rec Int (fun _ => Nat) 0 (fun x _ ih => Nat.add (Int.natAbs x) ih) xs

/-- The digit `d` read as the integer `d - K`, by one comparison. -/
def decK (d : Nat) : Int :=
  @Bool.casesOn (fun _ => Int) (Nat.ble K d) (Int.negSucc (Nat.sub (Nat.sub K d) 1))
    (Int.ofNat (Nat.sub d K))

/-- `unpk`, as a recursor term. -/
def unpkR (n N : Nat) : List Int :=
  @Nat.rec (fun _ => Nat → List Int) (fun _ => [])
    (fun _ ih N => decK (Nat.mod N B) :: ih (Nat.div N B)) n N

/-- `addV`, as a recursor term. -/
def addVR (xs ys : List Int) : List Int :=
  @List.rec Int (fun _ => List Int → List Int) (fun _ => [])
    (fun x _ ih ys => @List.casesOn Int (fun _ => List Int) ys []
      (fun y ys => Int.add x y :: ih ys)) xs ys

/-- `residual`, as a recursor term. -/
def residualR (xs as : List Int) : List Int :=
  @List.rec Int (fun _ => List Int → List Int) (fun _ => [])
    (fun x _ ih as => @List.casesOn Int (fun _ => List Int) as []
      (fun a as => Int.add (Int.mul x ALPHA_ONE) a :: ih as)) xs as

/-- `pre >> 8` if `pre > 0`, else 0, by one match on the sign. -/
def reluShr8 (pre : Int) : Int :=
  @Int.casesOn (fun _ => Int) pre (fun n => Int.ofNat (Nat.shiftRight n 8)) (fun _ => Int.ofNat 0)

/-- `reluShr8` of every entry. -/
def reluAll : List Int → List Int
  | [] => []
  | x :: xs => reluShr8 x :: reluAll xs

/-- `reluAll (unpk n N)` on natural numbers: a digit `d` stands for `pre = d - K`, so the
truncated subtraction `d - K` is `max pre 0`, and the shift by 8 follows. -/
def reluU (n N : Nat) : List Int :=
  @Nat.rec (fun _ => Nat → List Int) (fun _ => [])
    (fun _ ih N => Int.ofNat (Nat.shiftRight (Nat.sub (Nat.mod N B) K) 8) :: ih (Nat.div N B)) n N

/-- `hidden`, as a recursor term. -/
def hiddenR (accs bs : List Int) : List Int :=
  @List.rec Int (fun _ => List Int → List Int) (fun _ => [])
    (fun acc _ ih bs => @List.casesOn Int (fun _ => List Int) bs []
      (fun b bs => reluShr8 (Int.add acc (Int.mul b (Int.ofNat 256))) :: ih bs)) accs bs

/-- `finalStream`, as a recursor term. -/
def finalStreamR (rs os : List Int) : List Int :=
  @List.rec Int (fun _ => List Int → List Int) (fun _ => [])
    (fun r _ ih os => @List.casesOn Int (fun _ => List Int) os []
      (fun o os => Int.shiftRight (Int.add (Int.mul r (Int.ofNat 256)) o) 16 :: ih os)) rs os

/-- `mix`, as a recursor term. -/
def mixR (a0 a1 a2 : Int) (v0 v1 v2 : List Int) : List Int :=
  @List.rec Int (fun _ => List Int → List Int → List Int) (fun _ _ => [])
    (fun x0 _ ih v1 v2 => @List.casesOn Int (fun _ => List Int) v1 []
      (fun x1 r1 => @List.casesOn Int (fun _ => List Int) v2 []
        (fun x2 r2 =>
          Int.shiftRight (Int.add (Int.add (Int.mul a0 x0) (Int.mul a1 x1)) (Int.mul a2 x2)) 16
            :: ih r1 r2))) v0 v1 v2

/-- `expFix`, reading its tables with `nthR`. -/
def expFixR (W : Weights) (d : Int) : Int :=
  if d ≤ 0 then EXP_ONE
  else
    let u := Int.shiftRight d 8
    let n := Int.shiftRight u 24
    if 32 ≤ n then .ofNat 0
    else
      let b2 := Int.emod (Int.shiftRight u 16) 256
      let b1 := Int.emod (Int.shiftRight u 8) 256
      let b0 := Int.emod u 256
      let e := nthR 0 W.expN (Int.toNat n)
      let e := Int.shiftRight (Int.mul e (nthR 0 W.exp2 (Int.toNat b2))) 30
      let e := Int.shiftRight (Int.mul e (nthR 0 W.exp1 (Int.toNat b1))) 30
      Int.shiftRight (Int.mul e (nthR 0 W.exp0 (Int.toNat b0))) 30

/-- `softmaxWeights`, on `expFixR`. -/
def softmaxR (W : Weights) (s : Int × Int × Int) : Int × Int × Int :=
  let smax := s.1
  let smax := if s.2.1 > smax then s.2.1 else smax
  let smax := if s.2.2 > smax then s.2.2 else smax
  let e0 := expFixR W (Int.sub smax s.1)
  let e1 := expFixR W (Int.sub smax s.2.1)
  let e2 := expFixR W (Int.sub smax s.2.2)
  let den := Int.add (Int.add e0 e1) e2
  (Int.tdiv (Int.mul e0 ALPHA_ONE) den, Int.tdiv (Int.mul e1 ALPHA_ONE) den,
    Int.tdiv (Int.mul e2 ALPHA_ONE) den)

end

theorem nthR_eq {α : Type} (d : α) : ∀ (l : List α) (n : Nat), nthR d l n = nth d l n
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, n + 1 => by
    show nthR d xs n = nth d xs n
    exact nthR_eq d xs n

theorem dotR_eq : ∀ xs ys : List Int, dotR xs ys = dot xs ys
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    show Int.add (Int.mul x y) (dotR xs ys) = Int.add (Int.mul x y) (dot xs ys)
    rw [dotR_eq xs ys]

theorem sumAbsR_eq : ∀ xs : List Int, sumAbsR xs = sumAbs xs
  | [] => rfl
  | x :: xs => by
    show Nat.add (Int.natAbs x) (sumAbsR xs) = Int.natAbs x + sumAbs xs
    rw [sumAbsR_eq xs]
    rfl

theorem decK_eq (d : Nat) : decK d = Int.subNatNat d K := by
  unfold decK
  rw [Int.subNatNat_eq_coe]
  cases hb : Nat.ble K d with
  | true =>
    have hle : K ≤ d := Nat.le_of_ble_eq_true hb
    show Int.ofNat (d - K) = _
    simp only [Int.ofNat_eq_natCast]
    omega
  | false =>
    have hlt : ¬K ≤ d := fun h => by rw [Nat.ble_eq_true_of_le h] at hb; cases hb
    show Int.negSucc (K - d - 1) = _
    rw [Int.negSucc_eq]
    omega

theorem unpkR_eq : ∀ n N : Nat, unpkR n N = unpk n N
  | 0, _ => rfl
  | n + 1, N => by
    show decK (N % B) :: unpkR n (N / B) = Int.subNatNat (N % B) K :: unpk n (N / B)
    rw [unpkR_eq n, decK_eq]

theorem reluShr8_sub (d : Nat) :
    reluShr8 (Int.subNatNat d K) = Int.ofNat (Nat.shiftRight (Nat.sub d K) 8) := by
  by_cases hle : K ≤ d
  · rw [Int.subNatNat_of_le hle]
    rfl
  · have hlt : d < K := Nat.lt_of_not_le hle
    rw [Int.subNatNat_of_lt hlt, show Nat.sub d K = 0 from Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]
    rfl

theorem reluU_eq : ∀ n N : Nat, reluU n N = reluAll (unpk n N)
  | 0, _ => rfl
  | n + 1, N => by
    show Int.ofNat (Nat.shiftRight (Nat.sub (N % B) K) 8) :: reluU n (N / B) =
      reluShr8 (Int.subNatNat (N % B) K) :: reluAll (unpk n (N / B))
    rw [reluU_eq n, reluShr8_sub]

theorem addVR_eq : ∀ xs ys : List Int, addVR xs ys = addV xs ys
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    show Int.add x y :: addVR xs ys = Int.add x y :: addV xs ys
    rw [addVR_eq xs ys]

theorem residualR_eq : ∀ xs as : List Int, residualR xs as = residual xs as
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, a :: as => by
    show _ :: residualR xs as = _ :: residual xs as
    rw [residualR_eq xs as]

theorem reluShr8_eq (pre : Int) :
    reluShr8 pre = if pre > 0 then Int.shiftRight pre 8 else Int.ofNat 0 := by
  cases pre with
  | ofNat n =>
    show Int.ofNat (n >>> 8) = if Int.ofNat n > 0 then Int.ofNat (n >>> 8) else Int.ofNat 0
    by_cases h : Int.ofNat n > 0
    · simp only [h, ↓reduceIte]
    · have hn : n = 0 := by simp only [Int.ofNat_eq_natCast] at h; omega
      subst hn
      simp only [h, ↓reduceIte]
      rfl
  | negSucc n =>
    have h : ¬(Int.negSucc n > 0) := by omega
    show Int.ofNat 0 = if Int.negSucc n > 0 then _ else Int.ofNat 0
    simp only [h, ↓reduceIte]

theorem hiddenR_eq : ∀ accs bs : List Int, hiddenR accs bs = hidden accs bs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | acc :: accs, b :: bs => by
    show reluShr8 (Int.add acc (Int.mul b 256)) :: hiddenR accs bs = _ :: hidden accs bs
    rw [hiddenR_eq accs bs, reluShr8_eq]

/-- `hidden` is the bias times 256 added, then `reluShr8` of every entry. -/
theorem hidden_eq_reluAll : ∀ accs bs : List Int,
    hidden accs bs = reluAll (addV accs (scale (Int.ofNat 256) bs))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | acc :: accs, b :: bs => by
    have ih := hidden_eq_reluAll accs bs
    have e : Int.mul b 256 = Int.mul (Int.ofNat 256) b := Int.mul_comm b 256
    rw [← hiddenR_eq] at ih ⊢
    show reluShr8 (Int.add acc (Int.mul b 256)) :: hiddenR accs bs =
      reluShr8 (Int.add acc (Int.mul (Int.ofNat 256) b)) ::
        reluAll (addV accs (scale (Int.ofNat 256) bs))
    rw [ih, e]

theorem finalStreamR_eq : ∀ rs os : List Int, finalStreamR rs os = finalStream rs os
  | [], _ => rfl
  | _ :: _, [] => rfl
  | r :: rs, o :: os => by
    show _ :: finalStreamR rs os = _ :: finalStream rs os
    rw [finalStreamR_eq rs os]
    rfl

theorem mixR_eq (a0 a1 a2 : Int) : ∀ v0 v1 v2 : List Int,
    mixR a0 a1 a2 v0 v1 v2 = mix a0 a1 a2 v0 v1 v2
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | x0 :: r0, x1 :: r1, x2 :: r2 => by
    show _ :: mixR a0 a1 a2 r0 r1 r2 = _ :: mix a0 a1 a2 r0 r1 r2
    rw [mixR_eq a0 a1 a2 r0 r1 r2]

theorem expFixR_eq (W : Weights) (d : Int) : expFixR W d = expFix W d := by
  simp only [expFixR, expFix, nthR_eq]

theorem softmaxR_eq (W : Weights) (s : Int × Int × Int) : softmaxR W s = softmaxWeights W s := by
  simp only [softmaxR, softmaxWeights, expFixR_eq]

/-- `lincomb n x w`, computed on the packed rows `p = pkRows w`. `m` bounds the absolute entries
of `w` (`rowsOk`). Returns `none` when `m * sumAbs x` exceeds `K`, in which case a digit could
leave its window. -/
noncomputable def flc (n m : Nat) (x : List Int) (p : List Int) : Option (List Int) :=
  if m * sumAbsR x ≤ K then
    some (unpkR n (Int.toNat (Int.add (dotR x p) (.ofNat (K * ones n)))))
  else none

/-- `hidden (lincomb n x w) bin`, computed on the packed rows `p = pkRows w` and the packed bias
`pb = pkI (scale 256 bin)`: the bias is added while packed, and `reluU` reads the digits. `bb`
bounds the absolute entries of `scale 256 bin` (`biasOk`). -/
noncomputable def flcRelu (n m bb : Nat) (x p : List Int) (pb : Int) : Option (List Int) :=
  if m * sumAbsR x + bb ≤ K then
    some (reluU n (Int.toNat (Int.add (Int.add (dotR x p) pb) (.ofNat (K * ones n)))))
  else none

/-- The sum of four products `lincomb 128 z_h w_h`, added while packed and read back once. -/
noncomputable def fastAttn (m : Nat) (z0 z1 z2 z3 p0 p1 p2 p3 : List Int) : Option (List Int) :=
  if m * (sumAbsR z0 + sumAbsR z1 + sumAbsR z2 + sumAbsR z3) ≤ K then
    some (unpkR 128 (Int.toNat (Int.add
      (Int.add (Int.add (Int.add (dotR z0 p0) (dotR z1 p1)) (dotR z2 p2)) (dotR z3 p3))
      (.ofNat (K * ones 128)))))
  else none

/-- Every entry has absolute value at most `m`. -/
def bddB (m : Nat) : List Int → Bool
  | [] => true
  | e :: es => Nat.ble (Int.natAbs e) m && bddB m es

/-- Every row has `n` entries, each of absolute value at most `m`. -/
def rowsOk (n m : Nat) : List (List Int) → Bool
  | [] => true
  | r :: rs => (Nat.beq r.length n && bddB m r) && rowsOk n m rs

/-- The bias has `n` entries, and every entry times 256 has absolute value at most `bb`. -/
def biasOk (n bb : Nat) (bin : List Int) : Bool :=
  Nat.beq bin.length n && bddB bb (scale (Int.ofNat 256) bin)

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
  simp only [flc, sumAbsR_eq, unpkR_eq, dotR_eq] at h
  split at h
  · rename_i hle
    injection h with h
    rw [← h, ← hpk, iadd, Int.ofNat_eq_natCast]
    have := unpk_pkI (lincomb n x w) (bdd_mono hle _ hbd)
    rw [hlen] at this
    exact this.symm
  · contradiction

/-- The packed product with the packed bias, read through `reluU`, is the model's `hidden`. -/
theorem flcRelu_eq (n m bb : Nat) (x : List Int) (w : List (List Int)) (bin p : List Int)
    (pb : Int) (v : List Int) (hw : rowsOk n m w = true) (hb : biasOk n bb bin = true)
    (hp : p = pkRows w) (hpb : pb = pkI (scale (Int.ofNat 256) bin))
    (h : flcRelu n m bb x p pb = some v) : hidden (lincomb n x w) bin = v := by
  obtain ⟨hlen, hbd, hpk⟩ := lincomb_spec n m x w (rowsBdd_of_rowsOk n m w hw)
  simp only [biasOk, Bool.and_eq_true] at hb
  have hblen : (scale (Int.ofNat 256) bin).length = n := by
    rw [length_scale]
    exact Nat.eq_of_beq_eq_true hb.1
  have hbbd := bdd_of_bddB _ _ hb.2
  subst hp hpb
  simp only [flcRelu, sumAbsR_eq, dotR_eq, reluU_eq] at h
  split at h
  · rename_i hle
    injection h with h
    have hl : (lincomb n x w).length = (scale (Int.ofNat 256) bin).length := by rw [hlen, hblen]
    have hv := unpk_pkI (addV (lincomb n x w) (scale (Int.ofNat 256) bin))
      (bdd_mono hle _ (bdd_addV _ _ _ _ hbd hbbd))
    rw [length_addV _ _ hl, hblen, pkI_addV _ _ hl, hpk] at hv
    rw [hidden_eq_reluAll, ← h]
    exact congrArg reluAll hv.symm
  · contradiction

/-- One more product added to a sum: the length, the bound and the packing of the result. -/
theorem addV_step (n m : Nat) (acc : List Int) (q : Nat) (z : List Int) (w : List (List Int))
    (hw : RowsBdd n m w) (hl : acc.length = n) (hb : Bdd q acc) :
    (addV acc (lincomb n z w)).length = n ∧ Bdd (q + m * sumAbs z) (addV acc (lincomb n z w)) ∧
      pkI (addV acc (lincomb n z w)) = pkI acc + dot z (pkRows w) := by
  obtain ⟨l, b, k⟩ := lincomb_spec n m z w hw
  have e : acc.length = (lincomb n z w).length := by rw [hl, l]
  exact ⟨by rw [length_addV _ _ e, l], bdd_addV _ _ _ _ hb b, by rw [pkI_addV _ _ e, k]⟩

/-- The packed sum of the four products is the model's sum of the four products. -/
theorem fastAttn_eq (m : Nat) (z0 z1 z2 z3 : List Int) (w0 w1 w2 w3 : List (List Int))
    (p0 p1 p2 p3 v : List Int) (h0 : rowsOk 128 m w0 = true) (h1 : rowsOk 128 m w1 = true)
    (h2 : rowsOk 128 m w2 = true) (h3 : rowsOk 128 m w3 = true) (e0 : p0 = pkRows w0)
    (e1 : p1 = pkRows w1) (e2 : p2 = pkRows w2) (e3 : p3 = pkRows w3)
    (h : fastAttn m z0 z1 z2 z3 p0 p1 p2 p3 = some v) :
    addV (addV (addV (addV (List.replicate 128 (Int.ofNat 0)) (lincomb 128 z0 w0))
      (lincomb 128 z1 w1)) (lincomb 128 z2 w2)) (lincomb 128 z3 w3) = v := by
  obtain ⟨l1, b1, k1⟩ := addV_step 128 m _ 0 z0 w0 (rowsBdd_of_rowsOk _ _ _ h0)
    (List.length_replicate ..) (bdd_replicate 0 128)
  obtain ⟨l2, b2, k2⟩ := addV_step 128 m _ _ z1 w1 (rowsBdd_of_rowsOk _ _ _ h1) l1 b1
  obtain ⟨l3, b3, k3⟩ := addV_step 128 m _ _ z2 w2 (rowsBdd_of_rowsOk _ _ _ h2) l2 b2
  obtain ⟨l4, b4, k4⟩ := addV_step 128 m _ _ z3 w3 (rowsBdd_of_rowsOk _ _ _ h3) l3 b3
  subst e0 e1 e2 e3
  simp only [fastAttn, sumAbsR_eq, unpkR_eq, dotR_eq] at h
  split at h
  · rename_i hle
    injection h with h
    have hK : 0 + m * sumAbs z0 + m * sumAbs z1 + m * sumAbs z2 + m * sumAbs z3 ≤ K := by
      simp only [Nat.mul_add] at hle
      omega
    have hv := unpk_pkI _ (bdd_mono hK _ b4)
    rw [l4, k4, k3, k2, k1, pkI_replicate, Int.zero_add] at hv
    rw [← h]
    exact hv.symm
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
  bin : Nat

/-- The packed rows of the four matrices of the per-pair path: `wo` per head, `win`, `wout`, `u`;
and `bin`, the packed bias `pkI (scale 256 W.bin)`. -/
structure Packed where
  wo : List (List Int)
  win : List Int
  wout : List Int
  u : List Int
  bin : Int

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
  bin : biasOk 512 Bd.bin W.bin = true
  pwo : ∀ h, h < 4 → nth [] Pk.wo h = pkRows (nth [] W.wo h)
  pbin : Pk.bin = pkI (scale (Int.ofNat 256) W.bin)
  pwin : Pk.win = pkRows W.win
  pwout : Pk.wout = pkRows W.wout
  pu : Pk.u = pkRows W.u

/-! ### The tables, through packed products -/

/-- `keyScore` with both projections packed. -/
noncomputable def fastScore (W : Weights) (Bd : Bounds) (h : Nat) (x2 xj : List Int) :
    Option Int :=
  match flc 32 Bd.wq x2 (pkRows (nth [] W.wq h)), flc 32 Bd.wk xj (pkRows (nth [] W.wk h)) with
  | some q, some k => some (dotR q k)
  | _, _ => none

/-- `value` with the projection packed. -/
noncomputable def fastValue (W : Weights) (Bd : Bounds) (h : Nat) (xj : List Int) :
    Option (List Int) :=
  flc 32 Bd.wv xj (pkRows (nth [] W.wv h))

theorem fastScore_eq {W : Weights} {Bd : Bounds} {Pk : Packed} (hS : StaticOk W Bd Pk) (h : Nat)
    (hh : h < 4) (x2 xj : List Int) (s : Int) (e : fastScore W Bd h x2 xj = some s) :
    keyScore W h x2 xj = s := by
  unfold fastScore at e
  split at e
  · rename_i q k hq hk
    injection e with e
    unfold keyScore project
    rw [flc_eq _ _ _ _ _ _ (hS.wq h hh) rfl hq, flc_eq _ _ _ _ _ _ (hS.wk h hh) rfl hk,
      ← dotR_eq]
    exact e
  · contradiction

theorem fastValue_eq {W : Weights} {Bd : Bounds} {Pk : Packed} (hS : StaticOk W Bd Pk) (h : Nat)
    (hh : h < 4) (xj v : List Int) (e : fastValue W Bd h xj = some v) : value W h xj = v :=
  flc_eq _ _ _ _ _ _ (hS.wv h hh) rfl e

/-! ### The per-pair path -/

/-- The mixed value vector of head `h` for the pair `(a, b)`: scores and value vectors from the
tables. -/
noncomputable def fastMix (W : Weights) (T : Tables) (h a b : Nat) : List Int :=
  let alpha := softmaxR W
    (nthR 0 (nthR [] T.s0 h) a, nthR 0 (nthR [] T.s1 h) b, nthR 0 T.s2 h)
  mixR alpha.1 alpha.2.1 alpha.2.2 (nthR [] (nthR [] T.v0 h) a) (nthR [] (nthR [] T.v1 h) b)
    (nthR [] T.v2 h)

/-- `forward` of the model for the pair `(a, b)`, with the matrix products packed: the four heads
in one sum, the hidden layer with its bias and ReLU, the MLP output, the unembedding. -/
noncomputable def fastForward (W : Weights) (T : Tables) (Bd : Bounds) (Pk : Packed) (a b : Nat) :
    Option (List Int) :=
  (fastAttn Bd.wo (fastMix W T 0 a b) (fastMix W T 1 a b) (fastMix W T 2 a b) (fastMix W T 3 a b)
    (nthR [] Pk.wo 0) (nthR [] Pk.wo 1) (nthR [] Pk.wo 2) (nthR [] Pk.wo 3)).bind fun att =>
  let r := residualR (embed W EQ 2) att
  (flcRelu 512 Bd.win Bd.bin r Pk.win Pk.bin).bind fun m =>
  (flc 128 Bd.wout m Pk.wout).bind fun acc2 =>
  flc 113 Bd.u (finalStreamR r (addVR acc2 W.bout)) Pk.u

/-- `predict` of the model for a pair in range, through `fastForward`. -/
noncomputable def fastPredict (W : Weights) (T : Tables) (Bd : Bounds) (Pk : Packed) (a b : Nat) :
    Option Nat :=
  match fastForward W T Bd Pk a b with
  | some l => some (argmax l)
  | none => none

theorem headTerm_eq {W : Weights} {T : Tables} (hT : TablesOk W T) (h a b : Nat) (hh : h < 4)
    (ha : a < 113) (hb : b < 113) :
    headTerm W h (embed W a 0) (embed W b 1) (embed W EQ 2) =
      lincomb 128 (fastMix W T h a b) (nth [] W.wo h) := by
  simp only [fastMix, nthR_eq, softmaxR_eq, mixR_eq]
  unfold headTerm headOutput headScores
  rw [hT.s0 h hh a ha, hT.s1 h hh b hb, hT.s2 h hh, hT.v0 h hh a ha, hT.v1 h hh b hb, hT.v2 h hh]

theorem fastForward_sound {W : Weights} {T : Tables} {Bd : Bounds} {Pk : Packed}
    (hS : StaticOk W Bd Pk) (hT : TablesOk W T) (a b : Nat) (ha : a < 113) (hb : b < 113)
    (l : List Int) (e : fastForward W T Bd Pk a b = some l) : forward W a b = l := by
  unfold fastForward at e
  simp only [Option.bind_eq_some_iff, addVR_eq, residualR_eq, finalStreamR_eq, nthR_eq] at e
  obtain ⟨att, e0, m, e1, acc2, e2, e3⟩ := e
  have h0 := fastAttn_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hS.wo 0 (by decide)) (hS.wo 1 (by decide))
    (hS.wo 2 (by decide)) (hS.wo 3 (by decide)) (hS.pwo 0 (by decide)) (hS.pwo 1 (by decide))
    (hS.pwo 2 (by decide)) (hS.pwo 3 (by decide)) e0
  have h1 := flcRelu_eq _ _ _ _ _ _ _ _ _ hS.win hS.bin hS.pwin hS.pbin e1
  have h2 := flc_eq _ _ _ _ _ _ hS.wout hS.pwout e2
  have h3 := flc_eq _ _ _ _ _ _ hS.u hS.pu e3
  have t0 := headTerm_eq hT 0 a b (by decide) ha hb
  have t1 := headTerm_eq hT 1 a b (by decide) ha hb
  have t2 := headTerm_eq hT 2 a b (by decide) ha hb
  have t3 := headTerm_eq hT 3 a b (by decide) ha hb
  unfold forward attention mlpOutput mlpHidden unembed
  simp only [t0, t1, t2, t3, h0, h1, h2, h3]

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
