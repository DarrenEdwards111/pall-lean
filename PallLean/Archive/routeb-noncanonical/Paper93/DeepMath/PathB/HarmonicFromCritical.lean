import PallLean.Paper93.DeepMath.NFrame.SNFAlphaMinZero
import PallLean.Paper93.DeepMath.LPS.KnLaplacianConstKernel

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame
open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GraphSpectral

/-- At the trivial minimizer Φ = 0, the K_n Laplacian acts trivially: `(L · 0) = 0`,
    confirming Φ = 0 is in the kernel of L. (This is a strong form of "harmonic":
    Φ = 0 is harmonic for any graph.) -/
theorem zero_is_harmonic_Kn (n : ℕ) :
    (laplacian (completeAdj n)).mulVec (0 : Fin n → ℝ) = 0 := by
  ext i
  simp [Matrix.mulVec_zero]

/-- Constant-1 vector is also harmonic for K_n Laplacian (kernel includes constants). -/
theorem ones_is_harmonic_Kn (n : ℕ) :
    (laplacian (completeAdj n)).mulVec (fun _ => (1 : ℝ)) = 0 :=
  completeAdj_laplacian_ones n

end PallLean.Paper93.DeepMath.PathB
