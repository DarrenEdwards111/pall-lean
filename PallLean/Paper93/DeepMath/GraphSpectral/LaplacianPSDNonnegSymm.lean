import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianEdgeSum
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import Mathlib.Analysis.Matrix.PosDef

namespace PallLean.Paper93.DeepMath.GraphSpectral

open scoped Matrix

/-- The Laplacian of a symmetric real matrix is Hermitian. Over ℝ `star = id`, so the
conjugate transpose coincides with the transpose, and `IsSymm` upgrades to
`IsHermitian`. -/
lemma laplacian_isHermitian_of_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hSym : A.IsSymm) : (laplacian A).IsHermitian := by
  -- Aᴴ = Aᵀ over ℝ (trivial star), and Aᵀ = A by symmetry.
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact (laplacian_isSymm A hSym)

/-- For symmetric `A` with nonneg entries, the Laplacian quadratic form
    `v ⬝ᵥ (L · v)` is nonneg. This is the core inequality behind
    `Matrix.PosSemidef`. -/
lemma laplacian_dotProduct_mulVec_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hSym : A.IsSymm) (hNN : ∀ i j, 0 ≤ A i j) (v : Fin n → ℝ) :
    0 ≤ v ⬝ᵥ ((laplacian A).mulVec v) := by
  -- Unfold dotProduct to the explicit sum expected by `laplacian_quadForm_eq_edge_sum`.
  have hdp :
      v ⬝ᵥ ((laplacian A).mulVec v) =
        ∑ i, v i * ((laplacian A).mulVec v i) := by
    rfl
  -- Apply the edge-sum identity: 2 · (vᵀ L v) = ∑_{i,j} A_ij · (v_i − v_j)².
  have hedge := laplacian_quadForm_eq_edge_sum A hSym v
  -- The right-hand side of the identity is a sum of nonneg terms.
  have hRHS_nonneg :
      0 ≤ ∑ i, ∑ j, A i j * (v i - v j)^2 := by
    refine Finset.sum_nonneg ?_
    intros i _
    refine Finset.sum_nonneg ?_
    intros j _
    exact mul_nonneg (hNN i j) (sq_nonneg _)
  -- Transfer: from `2 * S = T` and `0 ≤ T`, deduce `0 ≤ S`.
  have h2S_nonneg :
      0 ≤ 2 * (∑ i, v i * ((laplacian A).mulVec v i)) := by
    rw [hedge]; exact hRHS_nonneg
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hS_nonneg :
      0 ≤ ∑ i, v i * ((laplacian A).mulVec v i) := by
    have := (mul_nonneg_iff_of_pos_left h2pos).mp h2S_nonneg
    exact this
  -- Fold the sum back to the dotProduct.
  rw [hdp]
  exact hS_nonneg

/-- For symmetric A with nonneg entries, the Laplacian `D − A` is PosSemidef.
    Proof: quadratic form equals `(1/2) · ∑_{i,j} A_ij · (φ_i − φ_j)² ≥ 0`. -/
theorem laplacian_posSemidef_of_symm_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hSym : A.IsSymm) (hNN : ∀ i j, 0 ≤ A i j) :
    (laplacian A).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (laplacian_isHermitian_of_symm A hSym) ?_
  intro v
  -- Over ℝ, `star v = v`.
  have hstar : (star v : Fin n → ℝ) = v := by
    funext i; exact star_trivial (v i)
  rw [hstar]
  exact laplacian_dotProduct_mulVec_nonneg A hSym hNN v

end PallLean.Paper93.DeepMath.GraphSpectral
