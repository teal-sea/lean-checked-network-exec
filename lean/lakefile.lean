import Lake
open Lake DSL

package «lcn-exec» where

-- Aeneas's Lean library, from the pinned submodule (toolchain/PINS.md).
require aeneas from "../toolchain/aeneas/backends/lean"

/-- This repository's self-contained Lean code: Aeneas translations (`LcnExec.Translated.*`),
universal engine proofs (`LcnExec.GeneralEngine.*`, `LcnExec.Engine.*`), adder and smoke proofs.
(`LcnExec.Engine.Trained*` depends on `TransformerInt.Gen.*`, which is generated on demand by
`scripts/gen_transformer_lean.py`, so it is exposed below as the opt-in `LcnExecTrained` target.) -/
@[default_target]
lean_lib LcnExec where
  globs := #[
    .andSubmodules `LcnExec.Smoke,
    .andSubmodules `LcnExec.Adder,
    .andSubmodules `LcnExec.Translated,
    .andSubmodules `LcnExec.GeneralEngine,
    .one `LcnExec.Engine.View,
    .one `LcnExec.Engine.Contract,
    .one `LcnExec.Engine.Load,
    .one `LcnExec.Engine.LoadComplete,
    .one `LcnExec.Engine.Dot,
    .one `LcnExec.Engine.Exponential,
    .one `LcnExec.Engine.Softmax,
    .one `LcnExec.Engine.Attention,
    .one `LcnExec.Engine.Mixing,
    .one `LcnExec.Engine.Projection,
    .one `LcnExec.Engine.Argmax,
    .one `LcnExec.Engine.Downstream,
    .one `LcnExec.Engine.Stages,
    .one `LcnExec.Engine.Correct
  ]

/-- Opt-in E3 trained-weights composition (requires `scripts/gen_transformer_lean.py` first). -/
lean_lib LcnExecTrained where
  globs := #[
    .one `LcnExec.Engine.Trained,
    .submodules `LcnExec.Engine.Trained,
    .one `LcnExec.Engine.TrainedFinal
  ]

/-- The gate 4 model, shared with the standalone pilot without copying its source. -/
lean_lib TransformerInt where
  globs := #[.andSubmodules `TransformerInt]

/-- The recurrent adder from lean-checked-network, vendored byte for byte by scripts/vendor.sh
(diff in evidence/vendored-diff.txt). -/
@[default_target]
lean_lib RnnAdder where
  roots := #[`RnnAdder.Network, `RnnAdder.Trained]

/-- The smoke test's translated `sum` as a native binary, for scripts/diff.sh. -/
lean_exe smoke_eval where
  root := `LcnExec.Smoke.Main

/-- The adder's translated `add_bits` and `add_u64` as a native binary, for scripts/diff.sh. -/
lean_exe adder_eval where
  root := `LcnExec.Adder.Main

/-- The Lean network `RnnAdder.Trained.net` as a native binary, for scripts/diff.sh. It links
neither Aeneas nor the translation. -/
lean_exe adder_net_eval where
  root := `LcnExec.Adder.NetMain
