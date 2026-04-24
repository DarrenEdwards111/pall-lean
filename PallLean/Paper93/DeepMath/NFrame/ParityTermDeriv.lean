/-
  PallLean/Paper93/DeepMath/NFrame/ParityTermDeriv.lean

  Derivative of the per-vertex parity term `parityTerm χ_v · ` at any
  point `φ_v ≠ 0`: since `Real.sign` is locally constant away from
  zero, `parityTerm χ_v ·` agrees with a constant function in a
  neighborhood of `φ_v`, and therefore has derivative `0` there.

  Kernel-only; no `sorry`, no bespoke axioms, no `True`.
-/
import PallLean.Paper93.DeepMath.NFrame.ParityPenalty
import PallLean.Paper93.DeepMath.NFrame.SignLocallyConst

namespace PallLean.Paper93.DeepMath.NFrame

/-- At `φ > 0`, `parityTerm chi_v ·` has derivative 0 (since sgn is locally constant).
    In a neighborhood of `φ > 0`, `parityTerm chi_v y = max 0 (1 - chi_v * 1) = max 0 (1 - chi_v)`,
    a constant. Hence derivative = 0. -/
theorem parityTerm_hasDerivAt_of_pos (chi_v phi_v : ℝ) (h : 0 < phi_v) :
    HasDerivAt (fun y => parityTerm chi_v y) 0 phi_v := by
  apply (hasDerivAt_const phi_v (max 0 (1 - chi_v))).congr_of_eventuallyEq
  filter_upwards [sign_locally_eq_one phi_v h] with y hy
  unfold parityTerm
  rw [hy]
  ring_nf

/-- At `φ < 0`, `parityTerm chi_v ·` has derivative 0. -/
theorem parityTerm_hasDerivAt_of_neg (chi_v phi_v : ℝ) (h : phi_v < 0) :
    HasDerivAt (fun y => parityTerm chi_v y) 0 phi_v := by
  apply (hasDerivAt_const phi_v (max 0 (1 + chi_v))).congr_of_eventuallyEq
  filter_upwards [sign_locally_eq_neg_one phi_v h] with y hy
  unfold parityTerm
  rw [hy]
  ring_nf

end PallLean.Paper93.DeepMath.NFrame
