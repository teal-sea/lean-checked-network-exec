module

public import Spec.Rust
public import Spec.Model
public import Spec.Weights
public import SepLogic.Public

/-!
# Public contracts for `predict` and `fast::predict_fast` of the `mlp` crate

The contracts are stated over the model of `Spec.Model`. Every contract uses `S.returns`,
which allows only a normal return: a call that panics (unwinds) cannot satisfy it. A contract
is also a guarantee of the absence of undefined behaviour for every call meeting its
precondition. The contracts are partial-correctness statements: they say nothing about
termination.

The weight tables are read through the statics `E1`, `E2` and `W2`. The contracts take as a
premise that those statics hold some bytes (`tablesStored`); this is a persistent fact about the
program's read-only data, not an ownership the caller gives up. For the compiled crate, the
statics hold exactly `E1Bytes`, `E2Bytes` and `W2Bytes` of `Spec.Weights` from program start.
-/

@[expose] public section
namespace Spec
open Iris Iris.BI Rust2Lean.Public

/-- The read-only statics `E1`, `E2` and `W2` (each a `[[i8; 128]; 113]`, alignment 1) hold the
bytes `e1`, `e2` and `w2`, row after row. -/
def tablesStored {PROP : Type} [BI PROP] (S : Vocab PROP) (e1 e2 w2 : List UInt8) : PROP :=
  iprop(
    -- the static `E1` holds the bytes `e1`,
    S.global Mir.Global.«static mlp::weights::E1» 1 e1 ∗
    -- the static `E2` holds the bytes `e2`,
    S.global Mir.Global.«static mlp::weights::E2» 1 e2 ∗
    -- and the static `W2` holds the bytes `w2`.
    S.global Mir.Global.«static mlp::weights::W2» 1 w2)

/-- The Rust value of type `Option<usize>` for `o`: `None` is variant 0 without fields, and
`Some(c)` is variant 1 with the single field `c`. -/
def optionUsizeVal {PROP : Type} [BI PROP] (S : Vocab PROP) : Option ℕ → S.Value
  | none => S.variantVal 0 (S.tupleVal [])
  | some c => S.variantVal 1 (S.tupleVal [S.intVal c])

/-- The Rust type `usize`. -/
abbrev usizeTy {PROP : Type} [BI PROP] (S : Vocab PROP) : S.Ty := S.intTy false 8

/-- Property 3. `predict(a, b)` never panics, for every `a: usize` and `b: usize`, and returns
the model's answer `predictModel` on the tables stored in `E1`, `E2` and `W2`: `None` when
`a >= 113` or `b >= 113`, and otherwise `Some(c)` with `c` the first index of the largest
score. -/
def predict_spec : Property := fun S =>
  -- For all inputs `a`, `b` and stored table bytes `e1`, `e2`, `w2`,
  ∀ (a b : ℕ) (e1 e2 w2 : List UInt8),
    -- PRECONDITIONS
    -- if `a` is a `usize`,
    a < 2 ^ 64 →
    -- `b` is a `usize`,
    b < 2 ^ 64 →
    -- and each table has `113 * 128` bytes,
    e1.length = P * HID → e2.length = P * HID → w2.length = P * HID →
    -- then, when the statics hold these tables,
    tablesStored S e1 e2 w2 ⊢
      -- `predict(a, b)` does not panic; on normal return,
      S.call Mir.Fn.«mlp::predict» [(S.intVal a, usizeTy S), (S.intVal b, usizeTy S)]
        (S.returns fun v => iprop(
          -- POSTCONDITIONS
          -- the result is the model's answer on these tables.
          ⌊v = optionUsizeVal S
            (predictModel (tableOfBytes e1) (tableOfBytes e2) (tableOfBytes w2) a b)⌋))

/-- Property 1. For all `a < 113` and `b < 113`, `predict(a, b)` returns
`Some((a + b) % 113)` on the tables of `src/weights.rs` (the statics' contents in the
compiled crate). -/
def predict_adds_mod_spec : Property := fun S =>
  -- For all inputs `a` and `b`,
  ∀ (a b : ℕ),
    -- PRECONDITIONS
    -- if `a < 113`
    a < P →
    -- and `b < 113`,
    b < P →
    -- then, when the statics hold the tables of `src/weights.rs`,
    tablesStored S E1Bytes E2Bytes W2Bytes ⊢
      -- `predict(a, b)` does not panic; on normal return,
      S.call Mir.Fn.«mlp::predict» [(S.intVal a, usizeTy S), (S.intVal b, usizeTy S)]
        (S.returns fun v => iprop(
          -- POSTCONDITIONS
          -- the result is `Some((a + b) % 113)`.
          ⌊v = optionUsizeVal S (some ((a + b) % P))⌋))

/-- Property 2. If `a >= 113` or `b >= 113`, then `predict(a, b)` returns `None` (whatever the
statics hold). -/
def predict_out_of_range_spec : Property := fun S =>
  -- For all inputs `a` and `b`,
  ∀ (a b : ℕ),
    -- PRECONDITIONS
    -- if `a` is a `usize`,
    a < 2 ^ 64 →
    -- `b` is a `usize`,
    b < 2 ^ 64 →
    -- and `a >= 113` or `b >= 113`,
    (P ≤ a ∨ P ≤ b) →
    -- then, with no further resources,
    ⊢
      -- `predict(a, b)` does not panic; on normal return,
      S.call Mir.Fn.«mlp::predict» [(S.intVal a, usizeTy S), (S.intVal b, usizeTy S)]
        (S.returns fun v => iprop(
          -- POSTCONDITIONS
          -- the result is `None`.
          ⌊v = optionUsizeVal S none⌋))

/-- Property 4. `fast::predict_fast(a, b)` has no undefined behaviour and never panics, for
every `a: usize` and `b: usize`; it returns the model's answer `predictModel` on the tables
stored in `E1`, `E2` and `W2`. -/
def predict_fast_spec : Property := fun S =>
  -- For all inputs `a`, `b` and stored table bytes `e1`, `e2`, `w2`,
  ∀ (a b : ℕ) (e1 e2 w2 : List UInt8),
    -- PRECONDITIONS
    -- if `a` is a `usize`,
    a < 2 ^ 64 →
    -- `b` is a `usize`,
    b < 2 ^ 64 →
    -- and each table has `113 * 128` bytes,
    e1.length = P * HID → e2.length = P * HID → w2.length = P * HID →
    -- then, when the statics hold these tables,
    tablesStored S e1 e2 w2 ⊢
      -- `predict_fast(a, b)` has no undefined behaviour and does not panic;
      -- on normal return,
      S.call Mir.Fn.«mlp::fast::predict_fast» [(S.intVal a, usizeTy S), (S.intVal b, usizeTy S)]
        (S.returns fun v => iprop(
          -- POSTCONDITIONS
          -- the result is the model's answer on these tables.
          ⌊v = optionUsizeVal S
            (predictModel (tableOfBytes e1) (tableOfBytes e2) (tableOfBytes w2) a b)⌋))

/-- Property 5. For every `a: usize` and `b: usize`, `fast::predict_fast(a, b)` and
`predict(a, b)` return the same value: calling `predict_fast(a, b)` and then `predict(a, b)`,
neither panics, and the two results are equal. -/
def predict_fast_eq_predict_spec : Property := fun S =>
  -- For all inputs `a`, `b` and stored table bytes `e1`, `e2`, `w2`,
  ∀ (a b : ℕ) (e1 e2 w2 : List UInt8),
    -- PRECONDITIONS
    -- if `a` is a `usize`,
    a < 2 ^ 64 →
    -- `b` is a `usize`,
    b < 2 ^ 64 →
    -- and each table has `113 * 128` bytes,
    e1.length = P * HID → e2.length = P * HID → w2.length = P * HID →
    -- then, when the statics hold these tables,
    tablesStored S e1 e2 w2 ⊢
      -- `predict_fast(a, b)` does not panic; on its normal return with `v`,
      S.call Mir.Fn.«mlp::fast::predict_fast» [(S.intVal a, usizeTy S), (S.intVal b, usizeTy S)]
        (S.returns fun v =>
          -- `predict(a, b)` does not panic; on its normal return with `w`,
          S.call Mir.Fn.«mlp::predict» [(S.intVal a, usizeTy S), (S.intVal b, usizeTy S)]
            (S.returns fun w => iprop(
              -- POSTCONDITIONS
              -- the two results are equal.
              ⌊v = w⌋)))

end Spec
