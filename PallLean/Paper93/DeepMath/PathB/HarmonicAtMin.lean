import PallLean.Paper93.DeepMath.NFrame.SNFAlphaMinZero
import PallLean.Paper93.DeepMath.LPS.KnLaplacianConstKernel

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame
open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GraphSpectral

/-- At the minimizer Φ = 0 of S_NF_alpha on K_n sum-zero subspace, Φ satisfies
    `(laplacian (completeAdj n)).mulVec Φ = 0` (vacuously, since Φ = 0).
    This is the start of "minimizer is harmonic". -/
theorem S_NF_alpha_minimizer_harmonic_zero (n : ℕ) :
    (laplacian (completeAdj n)).mulVec (0 : Fin n → ℝ) = 0 := by
  ext i
  simp [Matrix.mulVec_zero]

end PallLean.Paper93.DeepMath.PathB
