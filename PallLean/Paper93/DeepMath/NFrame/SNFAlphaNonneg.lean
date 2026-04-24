import PallLean.Paper93.DeepMath.LPS.KnLaplacianSumZeroQuad
import PallLean.Paper93.DeepMath.GadgetRank.IdentityQuad
import PallLean.Paper93.DeepMath.NFrame.SNF

/-!
# Non-negativity of the α-term of `S_NF` on `K_n` with sum-zero `Φ`

This file establishes that the α-term of the N-Frame action

  `S_NF_alpha α A Φ := α · Φᵀ (laplacian A) Φ`

is non-negative when `α ≥ 0` and `Φ : Fin n → ℝ` is sum-zero (and the
underlying adjacency is the complete-graph adjacency `completeAdj n`).

Since the parallel `SNF.lean` sibling is not yet in place, the α-term is
defined locally here via the quadratic form of the graph Laplacian.

Paper reference: §28.3 pp. 137–138 (action `S_NF[Φ; P]`, α-term).
-/

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GraphSpectral
open Matrix

/-- For `K_n` and a sum-zero `Φ`, the α-term of `S_NF` equals `α · n · ‖Φ‖²`.
    `S_NF_alpha` is defined in `SNF.lean` and imported here. -/
theorem S_NF_alpha_Kn_sumZero (α : ℝ) (n : ℕ) (phi : Fin n → ℝ)
    (hphi : ∑ i, phi i = 0) :
    S_NF_alpha α (completeAdj n) phi = α * (n : ℝ) * ∑ i, phi i * phi i := by
  unfold S_NF_alpha
  rw [completeAdj_laplacian_sumZero_quadForm n phi hphi]
  ring

/-- For `K_n`, sum-zero `Φ`, and `α ≥ 0`, the α-term of `S_NF` is non-negative. -/
theorem S_NF_alpha_Kn_nonneg (α : ℝ) (n : ℕ) (hα : 0 ≤ α) (phi : Fin n → ℝ)
    (hphi : ∑ i, phi i = 0) :
    0 ≤ S_NF_alpha α (completeAdj n) phi := by
  rw [S_NF_alpha_Kn_sumZero α n phi hphi]
  have h_sum_nn : 0 ≤ ∑ i, phi i * phi i := sum_sq_nonneg phi
  have h_n_nn : (0 : ℝ) ≤ n := by positivity
  positivity

end PallLean.Paper93.DeepMath.NFrame
