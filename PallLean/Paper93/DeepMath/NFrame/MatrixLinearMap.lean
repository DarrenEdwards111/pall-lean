import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PallLean.Paper93.DeepMath.NFrame

/-- The map `A ↦ A.mulVec v` is linear in A (for fixed v). -/
theorem mulVec_linear_in_matrix {n : ℕ} (v : Fin n → ℝ) :
    IsLinearMap ℝ (fun A : Matrix (Fin n) (Fin n) ℝ => A.mulVec v) := by
  constructor
  · intros A B
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intros j _
    ring
  · intros c A
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros j _
    ring

end PallLean.Paper93.DeepMath.NFrame
