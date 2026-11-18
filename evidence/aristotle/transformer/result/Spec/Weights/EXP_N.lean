module


/-! The `static` table `EXP_N` of `src/weights.rs`, entry for entry. -/

@[expose] public section
namespace Spec.Weights

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exponential table `EXP_N: [i64; 32]`. -/
def EXP_N : List Int := [
  1073741824, 395007542, 145315154, 53458458, 19666268, 7234816, 2661540, 979126, 360200, 132510,
  48748, 17933, 6597, 2427, 893, 328, 121, 44, 16, 6, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
]

end Spec.Weights
