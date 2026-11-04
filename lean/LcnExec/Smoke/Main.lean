import LcnExec.Translated.Smoke

/-! The smoke test's translated `sum` as a native binary, for scripts/diff.sh.

Input: one slice per line, whitespace-separated u32 values; an empty line is the empty slice.
Output, one line per input line: `ok <sum>`, `fail overflow` on integer overflow,
`fail <error>` on any other failure, `div` on divergence. -/

open Aeneas Aeneas.Std Result

namespace LcnExec.Smoke

def parseLine (line : String) : Except String (List U32) :=
  ((line.split Char.isWhitespace).toList.map (·.toString) |>.filter (· ≠ "")).mapM fun token =>
    match token.toNat? with
    | some n => if n < 2 ^ 32 then .ok ⟨BitVec.ofNat _ n⟩ else .error s!"not a u32: {token}"
    | none => .error s!"not a number: {token}"

def render (r : Result U32) : String :=
  match r.match with
  | .ok v => s!"ok {v.val}"
  | .vis (.fail .integerOverflow) _ => "fail overflow"
  | .vis (.fail e) _ => s!"fail {repr e}"
  | .div => "div"

def runLine (line : String) : Except String String := do
  let xs ← parseLine line
  if h : xs.length ≤ Usize.max then
    pure (render (smoke.sum (Slice.from xs h)))
  else
    throw "slice longer than Usize.max"

end LcnExec.Smoke

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut line ← stdin.getLine
  while line ≠ "" do
    match LcnExec.Smoke.runLine line.trimAsciiEnd.toString with
    | .ok out => stdout.putStrLn out
    | .error e =>
      IO.eprintln s!"bad input line: {e}"
      return 1
    line ← stdin.getLine
  return 0
