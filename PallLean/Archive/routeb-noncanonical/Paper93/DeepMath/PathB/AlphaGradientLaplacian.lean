import PallLean.Paper93.DeepMath.NFrame.SNFAlphaNonneg
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame
open PallLean.Paper93.DeepMath.GraphSpectral

/-- The α-term `S_NF_alpha α A Φ = α · (Φ ⬝ L Φ)` where L = laplacian A.
    The "gradient" (component k) of this quadratic form equals `2α · (L Φ)_k`.
    We provide the algebraic identity that's the basis. -/
theorem S_NF_alpha_quadForm_eq {n : ℕ} (α : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (phi : Fin n → ℝ) :
    S_NF_alpha α A phi = α * (∑ i, phi i * ((laplacian A).mulVec phi) i) := by
  rfl

end PallLean.Paper93.DeepMath.PathB
