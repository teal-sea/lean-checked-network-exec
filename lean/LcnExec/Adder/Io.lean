/-! The input and output format of the adder evaluators, for scripts/diff.sh. It imports nothing,
so the evaluator of the Lean network (`LcnExec/Adder/NetMain.lean`) does not link the translation.

Input, one case per line:
  `bits <a> <b> <sum>`  three strings of `0`/`1` (`-` is the empty string): the bits of the two
                        numbers, least significant first and of equal length, and the initial
                        contents of the `sum` buffer (any length)
  `u64 <a> <b>`         two decimal u64 values
Output, one line per input line:
  `some <carry> <sum>` or `none <sum>` for `bits`; `ok <sum> <carry>` for `u64`.
The Rust evaluator (rust/adder/src/bin/adder_eval.rs) reads and prints the same format. -/

namespace LcnExec.Adder.Io

/-- One input line, parsed. -/
inductive Case where
  | bits (xs : List (Bool × Bool)) (sum : List Bool)
  | u64 (a b : Nat)

def parseBits (token : String) : Except String (List Bool) :=
  if token = "-" then .ok []
  else token.toList.mapM fun c =>
    if c = '0' then .ok false
    else if c = '1' then .ok true
    else .error s!"not a bit: {c}"

def parseU64 (token : String) : Except String Nat :=
  match token.toNat? with
  | some n => if n < 2 ^ 64 then .ok n else .error s!"not a u64: {token}"
  | none => .error s!"not a number: {token}"

def parseLine (line : String) : Except String Case := do
  match (line.split Char.isWhitespace).toList.map (·.toString) |>.filter (· ≠ "") with
  | ["bits", a, b, sum] =>
    let a ← parseBits a
    let b ← parseBits b
    if a.length ≠ b.length then throw "the two numbers differ in length"
    pure (.bits (a.zip b) (← parseBits sum))
  | ["u64", a, b] => pure (.u64 (← parseU64 a) (← parseU64 b))
  | _ => throw s!"unknown line: {line}"

def showBit (b : Bool) : String := if b then "1" else "0"

def showBits (bits : List Bool) : String :=
  if bits.isEmpty then "-" else String.join (bits.map showBit)

/-- Reads cases from stdin and prints `eval` of each, one line per case. -/
def mainLoop (eval : Case → String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut line ← stdin.getLine
  while line ≠ "" do
    match parseLine line.trimAsciiEnd.toString with
    | .ok case => stdout.putStrLn (eval case)
    | .error e =>
      IO.eprintln s!"bad input line: {e}"
      return 1
    line ← stdin.getLine
  return 0

end LcnExec.Adder.Io
