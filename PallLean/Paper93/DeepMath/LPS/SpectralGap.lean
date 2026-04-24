import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PallLean.Paper93.DeepMath.LPS

noncomputable def lpsSpectralGapBound (p : ℕ) : ℝ := 2 * Real.sqrt p

theorem lpsSpectralGapBound_nonneg (p : ℕ) : 0 ≤ lpsSpectralGapBound p := by
  unfold lpsSpectralGapBound
  positivity

end PallLean.Paper93.DeepMath.LPS
