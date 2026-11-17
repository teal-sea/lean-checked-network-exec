module

public import Spec.Rust
public import Spec.Weights
public import SepLogic.Public

/-!
# Public contracts for `predict` of the `transformer` crate

The three properties of `SPEC.md`, for `pub fn predict(a: usize, b: usize) -> Option<usize>` of
`src/lib.rs`, stated in the public vocabulary of the translated program.

* Every contract uses `S.returns`, which admits only a normal return: a call that panics
  (unwinds) cannot satisfy it. The contracts are partial-correctness statements: they say what
  holds if the call returns, and that it does not panic or hit undefined behaviour; they say
  nothing about termination.
* The weight tables are read through the compiled `static`s of `src/weights.rs`; each contract
  takes as a premise that those statics hold the tables (`Spec.weightsStored`). This is a
  persistent fact about the program's read-only data (it holds from the program's start), not
  an ownership the caller gives up.
* `usize` arguments are the integers `0 ≤ a < 2^64`.
-/

@[expose] public section
namespace Spec
open Iris Iris.BI Rust2Lean.Public

/-- `Some(n)` as a value of `Option<usize>`. -/
def someUsize {PROP : Type} [BI PROP] (S : Vocab PROP) (n : Nat) : S.Value :=
  S.variantVal 1 (S.tupleVal [S.intVal n])

/-- `None` as a value of `Option<usize>`. -/
def noneUsize {PROP : Type} [BI PROP] (S : Vocab PROP) : S.Value :=
  S.variantVal 0 (S.tupleVal [])

/-- The call `predict(a, b)` for the `usize` values `a`, `b`. -/
def callPredict {PROP : Type} [BI PROP] (S : Vocab PROP) (a b : Nat)
    (Q : CallOutcome S.Value → PROP) : PROP :=
  S.call Mir.Fn.«transformer::predict»
    [(S.intVal a, S.argTy Mir.Fn.«transformer::predict» 0),
      (S.intVal b, S.argTy Mir.Fn.«transformer::predict» 1)] Q

/-- Property 1: if `a < 113` and `b < 113`, `predict(a, b)` returns `Some((a + b) % 113)`
(and does not panic). -/
def predict_in_range_spec : Property := fun S =>
  -- For all `usize` values `a`, `b`,
  ∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 →
    -- PRECONDITION: both inputs are below the modulus `P = 113`;
    a < 113 → b < 113 →
    -- given that the weight statics hold the tables of `src/weights.rs`,
    weightsStored S ⊢
      -- `predict(a, b)` does not panic, and on return
      callPredict S a b (S.returns fun v =>
        -- POSTCONDITION: the result is `Some((a + b) % 113)`.
        ⌊v = someUsize S ((a + b) % 113)⌋)

/-- Property 2: if `a ≥ 113` or `b ≥ 113`, `predict(a, b)` returns `None` (and does not
panic). -/
def predict_out_of_range_spec : Property := fun S =>
  -- For all `usize` values `a`, `b`,
  ∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 →
    -- PRECONDITION: one of the inputs is at least the modulus `P = 113`;
    (113 ≤ a ∨ 113 ≤ b) →
    -- given that the weight statics hold the tables of `src/weights.rs`,
    weightsStored S ⊢
      -- `predict(a, b)` does not panic, and on return
      callPredict S a b (S.returns fun v =>
        -- POSTCONDITION: the result is `None`.
        ⌊v = noneUsize S⌋)

/-- Property 3: `predict(a, b)` never panics, for every pair of `usize` values: no
out-of-bounds index, no division by zero and no arithmetic overflow can occur (nor any other
undefined behaviour); if the call returns, it returns normally. -/
def predict_no_panic_spec : Property := fun S =>
  -- For all `usize` values `a`, `b`,
  ∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 →
    -- given that the weight statics hold the tables of `src/weights.rs`,
    weightsStored S ⊢
      -- `predict(a, b)` does not panic: the only admitted outcome is a normal return.
      callPredict S a b (S.returns fun _ => ⌊True⌋)

end Spec
end
