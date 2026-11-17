import LcnExec.Translated.Adder
import LcnExec.Adder.Io

/-! The adder's translated `add_bits` and `add_u64` as a native binary, for scripts/diff.sh. The
format is in `LcnExec/Adder/Io.lean`. A translated function that does not return `ok` prints
`fail overflow` on integer overflow, `fail <error>` on any other failure, `div` on divergence. -/

open Aeneas Aeneas.Std Result

namespace LcnExec.Adder

open LcnExec.Adder.Io

def render {α : Type} (r : Result α) (show_ : α → String) : String :=
  match r.match with
  | .ok v => show_ v
  | .vis (.fail .integerOverflow) _ => "fail overflow"
  | .vis (.fail e) _ => s!"fail {repr e}"
  | .div => "div"

def eval : Case → String
  | .bits xs sum =>
    if h : xs.length ≤ Usize.max ∧ sum.length ≤ Usize.max then
      render (adder.add_bits (Slice.from xs h.1) (Slice.from sum h.2)) fun
        | (some carry, sum') => s!"some {showBit carry} {showBits sum'.val}"
        | (none, sum') => s!"none {showBits sum'.val}"
    else "slice longer than Usize.max"
  | .u64 a b =>
    render (adder.add_u64 ⟨BitVec.ofNat _ a⟩ ⟨BitVec.ofNat _ b⟩) fun (sum, carry) =>
      s!"ok {sum.val} {showBit carry}"

end LcnExec.Adder

def main : IO UInt32 := LcnExec.Adder.Io.mainLoop LcnExec.Adder.eval
