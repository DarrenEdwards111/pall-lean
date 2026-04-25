import PallLean.Paper93.DeepMath.NFrame.SNFAlphaMinZero
import PallLean.Paper93.DeepMath.PathB.MinimizerAtZeroKn

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame
open PallLean.Paper93.DeepMath.LPS

/-- At α-term EL critical point on K_n sum-zero with α > 0:
    the minimizer is Φ = 0 (since 0 is the unique minimum, and α-term is strictly positive
    for any nonzero sum-zero Φ). -/
theorem alpha_EL_unique_minimizer_Kn (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 1 ≤ n)
    (phi : Fin n → ℝ) (hphi : ∑ i, phi i = 0)
    (h_min : ∀ psi : Fin n → ℝ, ∑ i, psi i = 0 →
              S_NF_alpha α (completeAdj n) phi ≤ S_NF_alpha α (completeAdj n) psi) :
    S_NF_alpha α (completeAdj n) phi ≤ 0 := by
  have h := h_min 0 (by simp)
  rw [alpha_min_at_zero_value α n (le_of_lt hα)] at h
  exact h

end PallLean.Paper93.DeepMath.PathB
