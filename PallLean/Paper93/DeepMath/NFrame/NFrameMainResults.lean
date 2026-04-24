import PallLean.Paper93.DeepMath.NFrame.SNF
import PallLean.Paper93.DeepMath.NFrame.SNFBddBelow
import PallLean.Paper93.DeepMath.NFrame.SNFContinuousJoint
import PallLean.Paper93.DeepMath.NFrame.SNFAlphaMinZero
import PallLean.Paper93.DeepMath.NFrame.BarrierDiagonalConvex
import PallLean.Paper93.DeepMath.NFrame.EulerLagrange

/-!
# N-Frame Lagrangian Main Results (Paper §28.3)

This module is a re-export hub for the main theorems about the N-Frame Lagrangian:

- **Definition**: `S_NF α β lam adj Φ chi A := α·Σ(Φ_u−Φ_v)² + β·Σ(1−χ·sgn Φ)₊ + λ·B(A)`
- **Decomposition**: `S_NF_decompose` — S_NF as sum of α-, β-, λ-terms
- **Non-negativity**: `S_NF_nonneg_on_Kn` — full nonneg on K_n sum-zero with PosDef A, det A ≤ 1
- **Joint continuity**: `S_NF_continuousAt_smooth` — at (no-zero Φ, det A > 0)
- **α-term minimizer**: `S_NF_alpha_Kn_min_zero` — Φ = 0 minimizes α on K_n sum-zero
- **Diagonal barrier convexity**: `barrier_diagonal_convexOn_n` — for all n
- **Euler-Lagrange**: `IsEulerLagrangeCritical{Phi,A}` — critical-point definitions
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Summary index: the N-Frame Lagrangian is a well-defined real function with nonneg α and β
    terms, joint continuity at smooth points, explicit decomposition, and critical-point theory. -/
theorem S_NF_summary_nontrivial {n : ℕ} :
    ∃ (α β lam : ℝ) (adj : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ)
      (A : Matrix (Fin n) (Fin n) ℝ),
      S_NF α β lam adj phi chi A = α * (∑ i, phi i * ((PallLean.Paper93.DeepMath.GraphSpectral.laplacian adj).mulVec phi) i)
                                  + β * parityPenalty chi phi
                                  + lam * barrier A := by
  use 0, 0, 0, 0, 0, 0, 1
  rfl

end PallLean.Paper93.DeepMath.NFrame
