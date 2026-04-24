import Mathlib.Analysis.Matrix.PosDef

namespace PallLean.Paper93.DeepMath.GraphSpectral

open scoped Matrix

theorem zeroMatrix_posSemidef (N : ℕ) : (0 : Matrix (Fin N) (Fin N) ℝ).PosSemidef :=
  Matrix.PosSemidef.zero

/-- The concrete 2×2 graph Laplacian of the single-edge graph on two vertices. -/
def L2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; -1, 1]

/-- `L2` is symmetric (Hermitian over ℝ). -/
lemma L2_isHermitian : L2.IsHermitian := by
  unfold Matrix.IsHermitian L2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose, Matrix.transpose]

/-- For any vector `v : Fin 2 → ℝ`, the quadratic form `v ⬝ᵥ (L2 *ᵥ v)` equals
    `(v 0 - v 1)^2`. -/
lemma L2_quadForm (v : Fin 2 → ℝ) :
    v ⬝ᵥ (L2 *ᵥ v) = (v 0 - v 1) ^ 2 := by
  simp [L2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- The concrete 2×2 graph Laplacian is positive semidefinite. -/
theorem L2_posSemidef : L2.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg L2_isHermitian ?_
  intro v
  -- `star v = v` since ℝ has trivial star.
  have hstar : (star v : Fin 2 → ℝ) = v := by
    funext i; exact star_trivial (v i)
  rw [hstar, L2_quadForm]
  exact sq_nonneg _

end PallLean.Paper93.DeepMath.GraphSpectral
