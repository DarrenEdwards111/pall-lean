import Mathlib.Analysis.Matrix.PosDef

namespace PallLean.Paper93.DeepMath.GraphSpectral

theorem zeroMatrix_posSemidef (N : ℕ) : (0 : Matrix (Fin N) (Fin N) ℝ).PosSemidef :=
  Matrix.PosSemidef.zero
