import PallLean.Paper93.DeepMath.NFrame.ParityPenalty
import PallLean.Paper93.DeepMath.NFrame.RealSignFacts

namespace PallLean.Paper93.DeepMath.NFrame

/-- If `χ = +1` and `Φ > 0`, then `χ · sgn Φ = 1`. -/
theorem align_one_pos (phi_v : ℝ) (h : 0 < phi_v) :
    (1 : ℝ) * Real.sign phi_v = 1 := by
  rw [Real.sign_of_pos h, mul_one]

/-- If `χ = -1` and `Φ < 0`, then `χ · sgn Φ = 1`. -/
theorem align_negone_neg (phi_v : ℝ) (h : phi_v < 0) :
    (-1 : ℝ) * Real.sign phi_v = 1 := by
  rw [Real.sign_of_neg h]
  ring

/-- Per-vertex parity term is 0 when `χ · sgn Φ ≥ 1`. -/
theorem parityTerm_zero_of_aligned (chi_v phi_v : ℝ)
    (h : 1 ≤ chi_v * Real.sign phi_v) :
    parityTerm chi_v phi_v = 0 := by
  unfold parityTerm
  rw [max_eq_left]
  linarith

/-- Per-vertex parity term is 0 when χ = 1 and phi > 0. -/
theorem parityTerm_zero_of_pos_aligned (phi_v : ℝ) (h : 0 < phi_v) :
    parityTerm 1 phi_v = 0 := by
  apply parityTerm_zero_of_aligned
  rw [align_one_pos phi_v h]

/-- Per-vertex parity term is 0 when χ = -1 and phi < 0. -/
theorem parityTerm_zero_of_neg_aligned (phi_v : ℝ) (h : phi_v < 0) :
    parityTerm (-1) phi_v = 0 := by
  apply parityTerm_zero_of_aligned
  rw [align_negone_neg phi_v h]

end PallLean.Paper93.DeepMath.NFrame
