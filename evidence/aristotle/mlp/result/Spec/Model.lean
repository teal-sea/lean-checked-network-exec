module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Int

/-!
# Independent mathematical model of the `mlp` network

Written from the crate's `SPEC.md` and Rust source (`predict` in `src/lib.rs`), independently
of any generated code. A table is a function from (row, column) to an integer; the weight
statics `E1`, `E2`, `W2 : [[i8; 128]; 113]` are described by `tableOfBytes` of their
row-major byte contents.
-/

@[expose] public section

namespace Spec

/-- Number of rows of each table, and the modulus / number of candidate answers (`P` in Rust). -/
def P : ℕ := 113

/-- Number of hidden neurons, i.e. columns of each table (`HID` in Rust). -/
def HID : ℕ := 128

/-- A weight table: `t r k` is the entry in row `r`, column `k`. Only rows `r < P` and
columns `k < HID` are meaningful. -/
abbrev Table := ℕ → ℕ → ℤ

/-- Hidden neuron `k` for the input pair `(a, b)`: `(E1[a][k] + E2[b][k])^2`. -/
def hidden (E1 E2 : Table) (a b k : ℕ) : ℤ := (E1 a k + E2 b k) ^ 2

/-- Score of candidate answer `c` for the input pair `(a, b)`:
`∑_{k < HID} W2[c][k] * hidden[k]`. -/
def score (E1 E2 W2 : Table) (a b c : ℕ) : ℤ :=
  ∑ k ∈ Finset.range HID, W2 c k * hidden E1 E2 a b k

/-- `firstArgmax f n` is, for `n ≥ 1`, the smallest index `c < n` such that `f c` is maximal
among `f 0, …, f (n-1)`. By convention `firstArgmax f 0 = 0`. -/
def firstArgmax (f : ℕ → ℤ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if f (firstArgmax f n) < f n then n else firstArgmax f n

/-- The network's answer for an in-range pair `(a, b)`: the smallest candidate `c < P` whose
score is the largest. -/
def answer (E1 E2 W2 : Table) (a b : ℕ) : ℕ := firstArgmax (score E1 E2 W2 a b) P

/-- The intended result of `predict(a, b)` (and of `fast::predict_fast(a, b)`):
`Some (answer …)` when `a < P` and `b < P`, and `None` otherwise. -/
def predictModel (E1 E2 W2 : Table) (a b : ℕ) : Option ℕ :=
  if a < P ∧ b < P then some (answer E1 E2 W2 a b) else none

/-- The two's complement `i8` value of a byte: `x` if `x < 128`, else `x - 256`. -/
def i8OfByte (x : UInt8) : ℤ :=
  if x.toNat < 128 then (x.toNat : ℤ) else (x.toNat : ℤ) - 256

/-- The table stored row-major in the bytes `bs` (one two's complement `i8` per entry,
`HID` entries per row): entry `(r, k)` is the `i8` value of `bs[HID * r + k]`, or `0` if
that byte is absent. Only `k < HID` is meaningful. -/
def tableOfBytes (bs : List UInt8) : Table := fun r k =>
  match bs[HID * r + k]? with
  | some x => i8OfByte x
  | none => 0

/-- The `P * HID` bytes of a table stored row-major, each entry encoded as a two's complement
byte (entry value modulo 256). -/
def i8Bytes (t : Table) : List UInt8 :=
  (List.range (P * HID)).map fun i => UInt8.ofNat ((t (i / HID) (i % HID)) % 256).toNat

end Spec

end
