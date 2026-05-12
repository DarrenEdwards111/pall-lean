import PallLean.Paper93.DeepMath.NFrame.ParityAlignment

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- For χ = +1 and Φ > 0, the parity term equals 0 (perfect alignment). -/
theorem parityTerm_aligned_pos (phi_v : ℝ) (h : 0 < phi_v) :
    parityTerm 1 phi_v = 0 :=
  parityTerm_zero_of_pos_aligned phi_v h

/-- For χ = -1 and Φ < 0, the parity term equals 0 (perfect anti-alignment). -/
theorem parityTerm_aligned_neg (phi_v : ℝ) (h : phi_v < 0) :
    parityTerm (-1) phi_v = 0 :=
  parityTerm_zero_of_neg_aligned phi_v h

/-- At the minimizer with β > 0, parityPenalty must be 0 (since it's the smallest possible value).
    Hence at minimizer, all per-vertex parity terms are 0. -/
theorem parityPenalty_minimizer_eq_zero {n : ℕ} (chi phi : Fin n → ℝ)
    (h_align : ∀ i : Fin n, 1 ≤ chi i * Real.sign (phi i)) :
    parityPenalty chi phi = 0 :=
  parityPenalty_eq_zero_of_aligned chi phi h_align

end PallLean.Paper93.DeepMath.PathB
