import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.NFrame

open Matrix

/-- Dot product of a vector with itself equals sum of squares. -/
theorem dotProduct_self_eq_sum_sq {n : ℕ} (v : Fin n → ℝ) :
    dotProduct v v = ∑ i, v i * v i := by
  unfold dotProduct
  rfl

/-- `v ⬝ᵥ v ≥ 0` for real vectors. -/
theorem dotProduct_self_nonneg {n : ℕ} (v : Fin n → ℝ) :
    0 ≤ dotProduct v v := by
  rw [dotProduct_self_eq_sum_sq]
  exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- `v ⬝ᵥ v = 0 ↔ v = 0`. -/
theorem dotProduct_self_eq_zero {n : ℕ} (v : Fin n → ℝ) :
    dotProduct v v = 0 ↔ v = 0 := by
  rw [dotProduct_self_eq_sum_sq]
  constructor
  · intro h
    ext i
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ v j * v j := fun j _ => mul_self_nonneg _
    have hi : v i * v i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (Finset.mem_univ i)
    exact (mul_self_eq_zero.mp hi)
  · intro h; subst h; simp

end PallLean.Paper93.DeepMath.NFrame
