import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.GadgetRank

/-- If `M` is positive semidefinite, the quadratic form is nonneg.
    (Restatement of the PosSemidef definition.) -/
theorem posSemidef_quadForm_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.PosSemidef) (v : Fin n → ℝ) :
    0 ≤ ∑ i, v i * (M.mulVec v i) := by
  -- Use the `PosSemidef.dotProduct_mulVec_nonneg` characterisation:
  -- `0 ≤ star v ⬝ᵥ (M *ᵥ v)`.
  have h : 0 ≤ star v ⬝ᵥ (M.mulVec v) := hM.dotProduct_mulVec_nonneg v
  -- Unfold `dotProduct` and use that `star` is trivial on `ℝ` (`Pi.instTrivialStar`).
  simpa only [dotProduct, Pi.star_apply, star_trivial] using h

end PallLean.Paper93.DeepMath.GadgetRank
