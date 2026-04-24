import Mathlib.Analysis.Matrix.PosDef

namespace PallLean.Paper93.DeepMath

theorem mathlib_psd_bridge {N : ℕ} :
    (0 : Matrix (Fin N) (Fin N) ℝ).PosSemidef :=
  Matrix.PosSemidef.zero
