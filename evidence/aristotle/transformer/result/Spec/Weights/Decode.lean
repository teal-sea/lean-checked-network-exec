module

/-! Decoding of the compact weight literals of `Spec.Weights`. -/

@[expose] public section
namespace Spec.Weights

/-- The `i8` value of a byte `b < 256` (two's complement). -/
def i8OfByte (b : Nat) : Int := if b < 128 then (b : Int) else (b : Int) - 256

/-- The first `n` base-256 digits of `x`, least significant first, read as `i8` values. -/
def i8Row : Nat → Nat → List Int
  | 0, _ => []
  | n + 1, x => i8OfByte (x % 256) :: i8Row n (x / 256)

/-- Split a list into `n` consecutive blocks of `k` elements. -/
def chunks {α : Type} (k : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | n + 1, l => l.take k :: chunks k n (l.drop k)

end Spec.Weights
