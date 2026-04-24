import PallLean.Paper93.DeepMath.GadgetRank.OuterProduct
import Mathlib.LinearAlgebra.Matrix.Rank

namespace PallLean.Paper93.DeepMath.GadgetRank

/-- The outer product `outer v` is definitionally equal to `Matrix.vecMulVec v v`,
which is the factorisation `(col v) * (row v)` up to a singleton index. -/
theorem outer_eq_vecMulVec {n : ℕ} (v : Fin n → ℝ) :
    outer v = Matrix.vecMulVec v v := by
  -- Both sides are `Matrix.of (fun i j => v i * v j)` by definition.
  ext i j
  simp [outer, Matrix.vecMulVec_apply]

/-- The rank of the outer product `v ⊗ vᵀ` is at most `1`.

Strategy: `outer v = Matrix.vecMulVec v v`, and `Matrix.rank_vecMulVec_le` gives
the rank bound (via the factorisation `vecMulVec v v = (col v) * (row v)` with a
singleton middle index, so the rank is bounded by the width of the row factor,
which is `Fintype.card Unit = 1`). -/
theorem outer_rank_le_one {n : ℕ} (v : Fin n → ℝ) : (outer v).rank ≤ 1 := by
  -- Rewrite `outer v` as the canonical `vecMulVec` outer product.
  rw [outer_eq_vecMulVec]
  -- Apply Mathlib's `rank_vecMulVec_le`.
  exact Matrix.rank_vecMulVec_le v v

end PallLean.Paper93.DeepMath.GadgetRank
