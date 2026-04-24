import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.GraphSpectral

/-- Diagonal matrix's mulVec: `(diagonal d).mulVec v i = d i * v i`.

This is a direct wrapper around `Matrix.mulVec_diagonal` from Mathlib, specialised
to `Fin n` indices and real scalars. -/
theorem diagonal_mulVec_eq {n : ℕ} (d : Fin n → ℝ) (v : Fin n → ℝ) (i : Fin n) :
    (Matrix.diagonal d).mulVec v i = d i * v i :=
  Matrix.mulVec_diagonal d v i

end PallLean.Paper93.DeepMath.GraphSpectral
