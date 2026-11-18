import RnnAdder.Trained
import LcnExec.Adder.Io

/-! The Lean network `RnnAdder.Trained.net` as a native binary, for scripts/diff.sh: the
evaluator the theorems of `RnnAdder/Trained.lean` are about. It imports neither Aeneas nor the
translation. The format is in `LcnExec/Adder/Io.lean`.

`bits`: `RnnAdder.run` and `RnnAdder.finalCarry` on the given pairs when the `sum` buffer has
their length, and `none` with the buffer unchanged otherwise (property 2 of rust/adder/SPEC.md).
`u64`: the same two functions on the 64 bit pairs of `a` and `b`, with the sum bits packed by
`RnnAdder.bitsToNat`. -/

open RnnAdder RnnAdder.Trained

namespace LcnExec.Adder.Net

open LcnExec.Adder.Io

def eval : Case → String
  | .bits xs sum =>
    if sum.length ≠ xs.length then s!"none {showBits sum}"
    else s!"some {showBit (finalCarry net net.h0 xs)} {showBits (run net net.h0 xs)}"
  | .u64 a b =>
    let xs := (List.range 64).map fun j => (a.testBit j, b.testBit j)
    s!"ok {bitsToNat (run net net.h0 xs)} {showBit (finalCarry net net.h0 xs)}"

end LcnExec.Adder.Net

def main : IO UInt32 := LcnExec.Adder.Io.mainLoop LcnExec.Adder.Net.eval
