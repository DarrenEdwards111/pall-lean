import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PallLean.Paper93.DeepMath.LPS

def IsRamanujan (p d : ℕ) (gap : ℝ) : Prop := gap ≥ 2 * Real.sqrt (d - 1 : ℝ)

theorem ramanujanBound_zero_trivial : IsRamanujan 0 1 (2 * Real.sqrt 0) := by
  unfold IsRamanujan; simp

end PallLean.Paper93.DeepMath.LPS
