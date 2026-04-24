import PallLean.Paper93.DeepMath.GadgetRank.OuterProduct
import PallLean.Paper93.DeepMath.GadgetRank.OuterRankOne
import PallLean.Paper93.DeepMath.GadgetRank.RankPosOfNe

namespace PallLean.Paper93.DeepMath.GadgetRank

/-- For nonzero v, the outer product `v ⊗ v` has rank exactly 1.
    Uses `outer_rank_le_one` (upper bound) + `rank_pos_of_ne_zero` (lower bound via outer ≠ 0). -/
theorem outer_rank_eq_one {n : ℕ} (v : Fin n → ℝ) (hv : v ≠ 0) :
    (outer v).rank = 1 := by
  have h_le : (outer v).rank ≤ 1 := outer_rank_le_one v
  have h_outer_ne : outer v ≠ 0 := by
    intro h
    apply hv
    ext i
    have hii : (outer v) i i = 0 := by rw [h]; simp
    show v i = 0
    have hsq : v i * v i = 0 := by
      have heq : (outer v) i i = v i * v i := by
        simp [outer, Matrix.of_apply]
      rw [heq] at hii
      exact hii
    exact (mul_self_eq_zero.mp hsq)
  have h_ge : 1 ≤ (outer v).rank := rank_pos_of_ne_zero _ h_outer_ne
  omega

end PallLean.Paper93.DeepMath.GadgetRank
