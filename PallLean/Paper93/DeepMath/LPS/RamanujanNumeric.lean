import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PallLean.Paper93.DeepMath.LPS

/-- Ramanujan bound for complete graph K_n with n ≥ 4: second eigenvalue `-1`
    satisfies `|-1| ≤ 2 · √(d - 1)` where `d = n - 1` is the regularity. -/
theorem ramanujan_bound_Kn (n : ℕ) (hn : 4 ≤ n) :
    (1 : ℝ) ≤ 2 * Real.sqrt ((n : ℝ) - 2) := by
  have h2 : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) - 2) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    apply Real.sqrt_le_sqrt
    have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  linarith

end PallLean.Paper93.DeepMath.LPS
