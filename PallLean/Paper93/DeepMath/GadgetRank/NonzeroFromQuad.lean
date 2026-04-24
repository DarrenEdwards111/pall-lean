import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.GadgetRank

/-- If some quadratic form value is positive, the matrix is nonzero. -/
theorem ne_zero_of_quad_pos {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (hv : 0 < ∑ i, v i * (M.mulVec v i)) :
    M ≠ 0 := by
  intro h
  subst h
  simp [Matrix.mulVec, Matrix.zero_apply, dotProduct,
        Finset.sum_const_zero] at hv

end PallLean.Paper93.DeepMath.GadgetRank
