module

public import Spec.Rust
public import SepLogic.Public
public import Spec.Weights.TOK
public import Spec.Weights.POS
public import Spec.Weights.WQ
public import Spec.Weights.WK
public import Spec.Weights.WV
public import Spec.Weights.WO
public import Spec.Weights.WIN
public import Spec.Weights.BIN
public import Spec.Weights.WOUT
public import Spec.Weights.BOUT
public import Spec.Weights.U
public import Spec.Weights.EXP_N
public import Spec.Weights.EXP_2
public import Spec.Weights.EXP_1
public import Spec.Weights.EXP_0

/-!
# The weight statics of `src/weights.rs`

`Spec.Weights.TOK`, …, `Spec.Weights.EXP_0` (one file each under `Spec/Weights/`) are the
tables of `src/weights.rs`, entry for entry, nested exactly like the Rust arrays.
`weightsStored` says that the compiled `static`s hold these tables: their bytes are the
entries in row-major order, each `i8` as one two's-complement byte and each `i64` as eight
little-endian two's-complement bytes. It is a persistent fact about read-only memory, not an
ownership a caller gives up.
-/

@[expose] public section
namespace Spec
open Iris Iris.BI Rust2Lean.Public

/-- The byte of an `i8` value `x` (two's complement). -/
def i8Byte (x : Int) : UInt8 := (x % 256).toNat.toUInt8

/-- The bytes of an array of `i8` values, element after element. -/
def i8sBytes (xs : List Int) : List UInt8 := xs.map i8Byte

/-- The eight little-endian bytes of an `i64` value `x` (two's complement). -/
def i64Bytes (x : Int) : List UInt8 :=
  (List.range 8).map fun j => ((x % 2 ^ 64) / 2 ^ (8 * j) % 256).toNat.toUInt8

/-- The bytes of an array of `i64` values, element after element. -/
def i64sBytes (xs : List Int) : List UInt8 := xs.flatMap i64Bytes

/-- The `static` weight tables of `src/weights.rs`, as compiled, hold the tables of
`Spec.Weights`: the `i8` tables at alignment 1 and the `i64` tables at alignment 8. -/
def weightsStored {PROP : Type} [BI PROP] (S : Vocab PROP) : PROP := iprop(
  -- `TOK: [[i8; 128]; 114]`, row after row,
  S.global Mir.Global.«static transformer::weights::TOK» 1 (i8sBytes Weights.TOK.flatten) ∗
  -- `POS: [[i8; 128]; 3]`,
  S.global Mir.Global.«static transformer::weights::POS» 1 (i8sBytes Weights.POS.flatten) ∗
  -- `WQ: [[[i8; 32]; 128]; 4]`,
  S.global Mir.Global.«static transformer::weights::WQ» 1
    (i8sBytes Weights.WQ.flatten.flatten) ∗
  -- `WK: [[[i8; 32]; 128]; 4]`,
  S.global Mir.Global.«static transformer::weights::WK» 1
    (i8sBytes Weights.WK.flatten.flatten) ∗
  -- `WV: [[[i8; 32]; 128]; 4]`,
  S.global Mir.Global.«static transformer::weights::WV» 1
    (i8sBytes Weights.WV.flatten.flatten) ∗
  -- `WO: [[[i8; 128]; 32]; 4]`,
  S.global Mir.Global.«static transformer::weights::WO» 1
    (i8sBytes Weights.WO.flatten.flatten) ∗
  -- `WIN: [[i8; 512]; 128]`,
  S.global Mir.Global.«static transformer::weights::WIN» 1 (i8sBytes Weights.WIN.flatten) ∗
  -- `BIN: [i64; 512]`,
  S.global Mir.Global.«static transformer::weights::BIN» 8 (i64sBytes Weights.BIN) ∗
  -- `WOUT: [[i8; 128]; 512]`,
  S.global Mir.Global.«static transformer::weights::WOUT» 1 (i8sBytes Weights.WOUT.flatten) ∗
  -- `BOUT: [i64; 128]`,
  S.global Mir.Global.«static transformer::weights::BOUT» 8 (i64sBytes Weights.BOUT) ∗
  -- `U: [[i8; 113]; 128]`,
  S.global Mir.Global.«static transformer::weights::U» 1 (i8sBytes Weights.U.flatten) ∗
  -- and the exponential tables `EXP_N: [i64; 32]`, `EXP_2`, `EXP_1`, `EXP_0: [i64; 256]`.
  S.global Mir.Global.«static transformer::weights::EXP_N» 8 (i64sBytes Weights.EXP_N) ∗
  S.global Mir.Global.«static transformer::weights::EXP_2» 8 (i64sBytes Weights.EXP_2) ∗
  S.global Mir.Global.«static transformer::weights::EXP_1» 8 (i64sBytes Weights.EXP_1) ∗
  S.global Mir.Global.«static transformer::weights::EXP_0» 8 (i64sBytes Weights.EXP_0))

end Spec
