module

public import Mathlib

/-!
# Independent mathematical model of the `adder` crate

Pure definitions only (no proofs). They are written from `SPEC.md` and the doc comments of
`src/lib.rs` / `src/weights.rs`, independently of any generated code.

* `rippleCarry` / `rippleSum`: the ripple-carry adder of `SPEC.md` over a slice of bit pairs.
* `bitVal` / `val`: the value of a bit slice, least significant bit first.
* `netStep` / `netOut` / `netCarry`: the recurrent network evaluated by `step`, `out` and
  `carry`, with the weights of `weights.rs`, over mathematical integers.
-/

@[expose] public section

namespace Spec

/-! ## Ripple-carry adder -/

/-- Majority of three bits: `(a && b) || (a && c) || (b && c)`. -/
def maj (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- Ripple-carry adder started with incoming carry `c` over the bit pairs `xs = [(a_0,b_0), …]`:
returns the list of sum bits `s_i = a_i ^ b_i ^ c_i` and the final carry, where `c_0 = c` and
`c_{i+1} = maj a_i b_i c_i`. -/
def rippleFrom : Bool → List (Bool × Bool) → List Bool × Bool
  | c, [] => ([], c)
  | c, (a, b) :: xs =>
    let r := rippleFrom (maj a b c) xs
    ((a ^^ b ^^ c) :: r.1, r.2)

/-- The carries `[c_0, c_1, …, c_n]` of the ripple-carry adder on `xs`, starting from incoming
carry `c` (so `c_0 = c`, `c_{i+1} = maj a_i b_i c_i`). The list has length `xs.length + 1`. -/
def rippleCarriesFrom : Bool → List (Bool × Bool) → List Bool
  | c, [] => [c]
  | c, (a, b) :: xs => c :: rippleCarriesFrom (maj a b c) xs

/-- The carries `[c_0, …, c_n]` of `SPEC.md` for the slice `xs`, with `c_0 = false`. -/
def rippleCarries (xs : List (Bool × Bool)) : List Bool := rippleCarriesFrom false xs

/-- The final carry `c_n` of `SPEC.md` for the slice `xs` of `n` bit pairs (`c_0 = false`). -/
def rippleCarry (xs : List (Bool × Bool)) : Bool := (rippleFrom false xs).2

/-- The sum bits `[s_0, …, s_{n-1}]` of `SPEC.md` for the slice `xs` (`c_0 = false`),
`s_i = a_i ^ b_i ^ c_i`. -/
def rippleSum (xs : List (Bool × Bool)) : List Bool := (rippleFrom false xs).1

/-! ## Values of bit slices -/

/-- `bit(true) = 1`, `bit(false) = 0`. -/
def bitVal (b : Bool) : ℕ := if b then 1 else 0

/-- `val(v) = Σ_i bit(v[i]) * 2^i`, least significant bit first, as an unbounded natural. -/
def val : List Bool → ℕ
  | [] => 0
  | b :: bs => bitVal b + 2 * val bs

/-! ## The recurrent network (weights of `weights.rs`) -/

/-- Number of hidden units, `H`. -/
def H : ℕ := 4

/-- The hidden state `State = [bool; H]`, modelled as a list of `H` booleans (index `i` is
unit `i`). -/
abbrev State := List Bool

/-- Recurrent weights `WH`, one row per unit. -/
def WH : List (List ℤ) :=
  [[-12, 47, 39, -63], [-2, 18, 7, -80], [-2, 15, 14, -84], [4, -10, -17, 82]]
/-- Input weights `WXA` for the bit `a`, one per unit. -/
def WXA : List ℤ := [-6, -90, -99, 92]
/-- Input weights `WXB` for the bit `b`, one per unit. -/
def WXB : List ℤ := [-2, -90, -100, 92]
/-- Recurrent biases `BH`. -/
def BH : List ℤ := [36, 118, 127, -119]
/-- Sum-bit read-out weights `WO`, applied to the new state. -/
def WO : List ℤ := [-127, 63, 80, -120]
/-- Sum-bit weight `WOA` for the bit `a`. -/
def WOA : ℤ := 125
/-- Sum-bit weight `WOB` for the bit `b`. -/
def WOB : ℤ := 125
/-- Sum-bit bias `BO`. -/
def BO : ℤ := -73
/-- Carry read-out weights `WC`. -/
def WC : List ℤ := [28, -41, -34, 127]
/-- Carry read-out bias `BC`. -/
def BC : ℤ := -65
/-- Initial state `H0 = [false; 4]`. -/
def H0 : State := [false, false, false, false]
/-- The five states of `REACH` (not used by the evaluator). -/
def REACH : List State :=
  [[false, false, false, false], [true, true, true, false], [true, false, false, true],
   [false, true, true, false], [false, false, false, true]]

/-- `dot_b(w, h)`: sum of the weights `w[i]` at the positions `i` where `h[i]` is `true`. -/
def dotB (w : List ℤ) (h : State) : ℤ :=
  (List.zipWith (fun wi hi => if hi then wi else 0) w h).sum

/-- `thr(z)`: the threshold activation `z > 0`. -/
def thr (z : ℤ) : Bool := decide (0 < z)

/-- `bit(b)` as an integer, used to write the affine pre-activations. -/
def bitZ (b : Bool) : ℤ := if b then 1 else 0

/-- `step(h, a, b)`: entry `i` is `[ WH[i]·h + WXA[i]·a + WXB[i]·b + BH[i] > 0 ]`. -/
def netStep (h : State) (a b : Bool) : State :=
  (List.range H).map fun i =>
    thr (dotB (WH.getD i []) h + WXA.getD i 0 * bitZ a + WXB.getD i 0 * bitZ b + BH.getD i 0)

/-- `out(h, a, b) = [ WO·(step h a b) + WOA·a + WOB·b + BO > 0 ]`. -/
def netOut (h : State) (a b : Bool) : Bool :=
  thr (dotB WO (netStep h a b) + WOA * bitZ a + WOB * bitZ b + BO)

/-- `carry(h) = [ WC·h + BC > 0 ]`. -/
def netCarry (h : State) : Bool := thr (dotB WC h + BC)

/-- Runs the network from state `h` over the bit pairs `xs` (least significant first), as the
loop of `add_bits` does: returns the emitted sum bits and the final state. -/
def netRunFrom : State → List (Bool × Bool) → List Bool × State
  | h, [] => ([], h)
  | h, (a, b) :: xs =>
    let r := netRunFrom (netStep h a b) xs
    (netOut h a b :: r.1, r.2)

/-- The sum bits written by `add_bits(xs, sum)` (when the lengths agree), started from `H0`. -/
def netSum (xs : List (Bool × Bool)) : List Bool := (netRunFrom H0 xs).1

/-- The carry returned by `add_bits(xs, sum)` (when the lengths agree): `carry` of the final
state. -/
def netFinalCarry (xs : List (Bool × Bool)) : Bool := netCarry (netRunFrom H0 xs).2

/-! ## 64-bit helpers for `add_u64` -/

/-- The 64 bits of `x : u64` (as a natural `< 2^64`), least significant first. -/
def bits64 (x : ℕ) : List Bool := (List.range 64).map fun i => x.testBit i

/-- The 64 bit pairs fed by `add_u64(a, b)`, least significant first. -/
def pairs64 (a b : ℕ) : List (Bool × Bool) := List.zip (bits64 a) (bits64 b)

/-- `a.overflowing_add(b)` for `u64` values given as naturals: `((a + b) mod 2^64, a + b ≥ 2^64)`. -/
def overflowingAdd64 (a b : ℕ) : ℕ × Bool := ((a + b) % 2 ^ 64, decide (2 ^ 64 ≤ a + b))

end Spec
