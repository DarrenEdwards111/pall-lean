import Mathlib.Analysis.Matrix.PosDef

namespace PallLean.Paper93.DeepMath.Amplituhedron

/-- Positivity preservation: a (real) positive-definite matrix has positive determinant.

This is a thin wrapper around Mathlib's `Matrix.PosDef.det_pos`. -/
theorem posDef_det_pos {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) (hM : M.PosDef) :
    0 < M.det :=
  hM.det_pos

end PallLean.Paper93.DeepMath.Amplituhedron
