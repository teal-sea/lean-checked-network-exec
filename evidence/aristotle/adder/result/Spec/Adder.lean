module

public import Spec.Rust
public import Spec.Model
public import SepLogic.Public

/-!
# Public contracts for the `adder` crate

Contracts for `step`, `out`, `carry`, `add_bits` and `add_u64` of `src/lib.rs`, stated over
the pure model of `Spec.Model`. Every contract uses `S.returns`, which allows only a normal
return: a call that panics (unwinds) cannot satisfy it. The contracts are partial-correctness
statements: they say nothing about termination.

The weight tables `WH`, `WO` and `WC` are read through their compiled read-only constants;
the contracts take as a premise that those constants hold the little-endian bytes of the
weights of `weights.rs` (`weightsStored`). This is a persistent fact about the program's
read-only data, not an ownership the caller must give up.
-/

@[expose] public section
namespace Spec
open Iris Iris.BI Rust2Lean.Public

/-! ## Stored weight tables -/

/-- The four little-endian bytes of an `i32` value `x` (two's complement). -/
def i32Bytes (x : ℤ) : List UInt8 :=
  let u := (x % 2 ^ 32).toNat
  [(u % 256).toUInt8, (u / 256 % 256).toUInt8, (u / 65536 % 256).toUInt8,
    (u / 16777216 % 256).toUInt8]

/-- The bytes of an array of `i32` values, element after element. -/
def i32sBytes (xs : List ℤ) : List UInt8 := xs.flatMap i32Bytes

/-- The compiled constants read by the crate hold the weight tables of `weights.rs`:
`WH` (as a `[[i32; 4]; 4]`, row after row), `WO` and `WC`, each 4-byte aligned. -/
def weightsStored {PROP : Type} [BI PROP] (S : Vocab PROP) : PROP := iprop(
  -- the 64-byte constant holds `WH`, row after row,
  S.global Mir.Global.«const [64 bytes] 802a34efed5a47d7» 4 (i32sBytes WH.flatten) ∗
  -- one 16-byte constant holds `WO`,
  S.global Mir.Global.«const [16 bytes] 13cda269b0321f68» 4 (i32sBytes WO) ∗
  -- and the other 16-byte constant holds `WC`.
  S.global Mir.Global.«const [16 bytes] 4f51ea92c411eebc» 4 (i32sBytes WC))

/-! ## Representations -/

/-- The value of a `State = [bool; 4]` whose units are the entries of `h`. -/
def stateVal {PROP : Type} [BI PROP] (S : Vocab PROP) (h : State) : S.Value :=
  S.tupleVal (h.map S.boolVal)

/-- The Rust type `[bool; 4]` (`State`). -/
def stateTy {PROP : Type} [BI PROP] (S : Vocab PROP) : S.Ty := S.arrayTy S.boolTy 4

/-- A share `q` of the bit pairs `xs` of a `[(bool, bool)]` starting at `p`, viewed as its
`2 * xs.len()` bytes, i.e. as a `[bool; 2 n]`: pair `i` occupies byte `2 i` (its first
component) and byte `2 i + 1` (its second component). For an empty slice this still
asserts that `p` is a valid (zero-sized) location, as a Rust reference guarantees. -/
def pairCells {PROP : Type} [BI PROP] (S : Vocab PROP) (q : Qp) (p : S.Ptr)
    (xs : List (Bool × Bool)) : PROP :=
  S.pointsToF p q (S.arrayTy S.boolTy (2 * xs.length))
    (S.tupleVal (xs.flatMap fun ab => [S.boolVal ab.1, S.boolVal ab.2]))

/-- Full ownership of the elements `v` of a `[bool]` starting at `p`, viewed as a
`[bool; v.len()]`. For an empty slice this still asserts that `p` is a valid (zero-sized)
location, as a Rust reference guarantees. -/
def boolCells {PROP : Type} [BI PROP] (S : Vocab PROP) (p : S.Ptr) (v : List Bool) : PROP :=
  S.pointsToF p 1 (S.arrayTy S.boolTy v.length) (S.tupleVal (v.map S.boolVal))

/-- `Some(c)` as a value of `Option<bool>`. -/
def someBool {PROP : Type} [BI PROP] (S : Vocab PROP) (c : Bool) : S.Value :=
  S.variantVal 1 (S.tupleVal [S.boolVal c])

/-- `None` as a value of `Option<bool>`. -/
def noneBool {PROP : Type} [BI PROP] (S : Vocab PROP) : S.Value :=
  S.variantVal 0 (S.tupleVal [])

/-! ## `step`, `out`, `carry` -/

/-- `step(h, a, b)` never panics, for every state `h` and bits `a`, `b`, and returns the
state `netStep h a b` of the model, giving the borrowed state back. -/
def step_spec : Property := fun S =>
  -- For every pointer `p`, share `q`, state `h` and bits `a`, `b`,
  ∀ (p : S.Ptr) (q : Qp) (h : State) (a b : Bool),
    -- PRECONDITIONS
    -- if the state has four units,
    h.length = 4 →
    -- the weight constants hold the weights,
    weightsStored S ∗
    -- and we own a share of the state `h` behind `p`,
    S.pointsToF p q (stateTy S) (stateVal S h) ⊢
      -- then `step(&h, a, b)` does not panic; on normal return,
      S.call Mir.Fn.«adder::step»
        [(S.ptrVal p, S.argTy Mir.Fn.«adder::step» 0), (S.boolVal a, S.boolTy),
          (S.boolVal b, S.boolTy)]
        (S.returns fun v => iprop(
          -- POSTCONDITIONS
          -- the returned state is the model's next state,
          ⌊v = stateVal S (netStep h a b)⌋ ∗
          -- and the share of `h` is given back unchanged.
          S.pointsToF p q (stateTy S) (stateVal S h)))

/-- `out(h, a, b)` never panics and returns the sum bit `netOut h a b` of the model. -/
def out_spec : Property := fun S =>
  -- For every pointer `p`, share `q`, state `h` and bits `a`, `b`,
  ∀ (p : S.Ptr) (q : Qp) (h : State) (a b : Bool),
    -- PRECONDITIONS
    -- if the state has four units,
    h.length = 4 →
    -- the weight constants hold the weights,
    weightsStored S ∗
    -- and we own a share of the state `h` behind `p`,
    S.pointsToF p q (stateTy S) (stateVal S h) ⊢
      -- then `out(&h, a, b)` does not panic; on normal return,
      S.call Mir.Fn.«adder::out»
        [(S.ptrVal p, S.argTy Mir.Fn.«adder::out» 0), (S.boolVal a, S.boolTy),
          (S.boolVal b, S.boolTy)]
        (S.returns fun v => iprop(
          -- POSTCONDITIONS
          -- the returned bit is the model's sum bit,
          ⌊v = S.boolVal (netOut h a b)⌋ ∗
          -- and the share of `h` is given back unchanged.
          S.pointsToF p q (stateTy S) (stateVal S h)))

/-- `carry(h)` never panics and returns the carry `netCarry h` of the model. -/
def carry_spec : Property := fun S =>
  -- For every pointer `p`, share `q` and state `h`,
  ∀ (p : S.Ptr) (q : Qp) (h : State),
    -- PRECONDITIONS
    -- if the state has four units,
    h.length = 4 →
    -- the weight constants hold the weights,
    weightsStored S ∗
    -- and we own a share of the state `h` behind `p`,
    S.pointsToF p q (stateTy S) (stateVal S h) ⊢
      -- then `carry(&h)` does not panic; on normal return,
      S.call Mir.Fn.«adder::carry»
        [(S.ptrVal p, S.argTy Mir.Fn.«adder::carry» 0)]
        (S.returns fun v => iprop(
          -- POSTCONDITIONS
          -- the returned bit is the model's carry,
          ⌊v = S.boolVal (netCarry h)⌋ ∗
          -- and the share of `h` is given back unchanged.
          S.pointsToF p q (stateTy S) (stateVal S h)))

/-! ## `add_bits` -/

/-- The common shape of the `add_bits` contracts: for valid slice references `xs` (a share
`q` of the pairs `xs` at `xp`) and `sum` (the bits `sum` at `sp`, owned), the call does not
panic, gives the share of `xs` back, and on normal return satisfies `post v sum'`, where `v`
is the returned `Option<bool>` and `sum'` the final contents of `sum`. -/
def add_bits_contract {PROP : Type} [BI PROP] (S : Vocab PROP)
    (post : List (Bool × Bool) → List Bool → S.Value → List Bool → Prop) : Prop :=
  -- For every pair of pointers, share `q`, pairs `xs` and bits `sum`,
  ∀ (xp sp : S.Ptr) (q : Qp) (xs : List (Bool × Bool)) (sum : List Bool),
    -- PRECONDITIONS
    -- if `xs` is a valid `&[(bool, bool)]` of length `xs.length`,
    ⌊S.loadable (S.slicePtrVal xp xs.length) (S.argTy Mir.Fn.«adder::add_bits» 0)⌋ ∗
    -- `sum` is a valid `&mut [bool]` of length `sum.length`,
    ⌊S.loadable (S.slicePtrVal sp sum.length) (S.argTy Mir.Fn.«adder::add_bits» 1)⌋ ∗
    -- the weight constants hold the weights,
    weightsStored S ∗
    -- we own a share of the pairs of `xs`,
    pairCells S q xp xs ∗
    -- and we own the elements of `sum`,
    boolCells S sp sum ⊢
      -- then `add_bits(xs, sum)` does not panic; on normal return,
      S.call Mir.Fn.«adder::add_bits»
        [(S.slicePtrVal xp xs.length, S.argTy Mir.Fn.«adder::add_bits» 0),
          (S.slicePtrVal sp sum.length, S.argTy Mir.Fn.«adder::add_bits» 1)]
        (S.returns fun v => iprop(
          -- POSTCONDITIONS
          -- there are final contents `sum'` of `sum` such that
          ∃ sum' : List Bool,
            -- the result and final contents satisfy `post`,
            ⌊post xs sum v sum'⌋ ∗
            -- the share of `xs` is given back unchanged,
            pairCells S q xp xs ∗
            -- and we own the elements of `sum`, now holding `sum'`.
            boolCells S sp sum'))

/-- Property 2: if `sum.len() != xs.len()`, `add_bits(xs, sum)` returns `None` and leaves
every element of `sum` unchanged (and does not panic). -/
def add_bits_length_mismatch_spec : Property := fun S =>
  add_bits_contract S fun xs sum v sum' =>
    -- If the lengths differ,
    sum.length ≠ xs.length →
      -- the result is `None` and `sum` is unchanged.
      v = noneBool S ∧ sum' = sum

/-- Property 3: if `sum.len() == xs.len()`, `add_bits(xs, sum)` returns `Some(c_n)` and
leaves `sum[i] = s_i` for every `i < n`: the ripple-carry adder (and does not panic). -/
def add_bits_ripple_spec : Property := fun S =>
  add_bits_contract S fun xs sum v sum' =>
    -- If the lengths agree,
    sum.length = xs.length →
      -- the result is `Some` of the final ripple carry,
      v = someBool S (rippleCarry xs) ∧
      -- and `sum` holds the ripple-carry sum bits.
      sum' = rippleSum xs

/-- Property 4: if `sum.len() == xs.len() = n`, then on return `add_bits(xs, sum)` gives
`Some(c)` with `val(sum) + 2^n * bit(c) = val(a's) + val(b's)` (and does not panic). -/
def add_bits_adds_spec : Property := fun S =>
  add_bits_contract S fun xs sum v sum' =>
    -- If the lengths agree,
    sum.length = xs.length →
      -- the result is `Some(c)` for some bit `c`,
      ∃ c : Bool, v = someBool S c ∧
        -- and the final sum and carry add up to `A + B`.
        val sum' + 2 ^ xs.length * bitVal c = val (xs.map Prod.fst) + val (xs.map Prod.snd)

/-! ## `add_u64` -/

/-- Property 5: `add_u64(a, b)` never panics and returns `a.overflowing_add(b)`:
`((a + b) mod 2^64, a + b ≥ 2^64)`. -/
def add_u64_spec : Property := fun S =>
  -- For all `a` and `b`,
  ∀ (a b : ℕ),
    -- PRECONDITIONS
    -- if `a` and `b` are `u64` values,
    a < 2 ^ 64 → b < 2 ^ 64 →
    -- and the weight constants hold the weights,
    weightsStored S ⊢
      -- then `add_u64(a, b)` does not panic; on normal return,
      S.call Mir.Fn.«adder::add_u64»
        [(S.intVal a, S.intTy false 8), (S.intVal b, S.intTy false 8)]
        (S.returns fun v => iprop(
          -- POSTCONDITIONS
          -- the result is the pair `a.overflowing_add(b)`.
          ⌊v = S.tupleVal [S.intVal (overflowingAdd64 a b).1,
            S.boolVal (overflowingAdd64 a b).2]⌋))

/-! ## Property 1 -/

/-- Property 1: no call to `step`, `out`, `carry`, `add_bits` or `add_u64` panics, for any
arguments. Each conjunct is a contract whose postcondition `S.returns` excludes unwinding;
the `add_bits` conjunct covers both length cases. -/
def no_panics_spec : Property := fun S =>
  step_spec S ∧ out_spec S ∧ carry_spec S ∧
  add_bits_contract S (fun _ _ _ _ => True) ∧ add_u64_spec S

end Spec
