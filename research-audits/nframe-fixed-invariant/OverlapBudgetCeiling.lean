import PallLean.Paper93.DeepMath.NFrame.LogDetEigenvalues
import Mathlib.Tactic

namespace OverlapBudgetCeiling

/-- The overlap-normalized trace certificate cannot exceed ambient dimension. -/
theorem normalized_mass_le_dimension {N : ℕ} (x : Fin N → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hu : ∀ i, x i ≤ L) :
    (∑ i, x i) / (1 + L) ≤ (N : ℝ) := by
  apply (div_le_iff₀ (by positivity : 0 < 1 + L)).2
  have hs : (∑ i, x i) ≤ (N : ℝ) * L := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hu i)
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Upper bound for the very same spectral log sum, not a substitute invariant. -/
theorem spectral_log_upper {N : ℕ} (x : Fin N → ℝ) (L : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hu : ∀ i, x i ≤ L) :
    (∑ i, Real.log (1 + x i)) ≤ (N : ℝ) * Real.log (1 + L) := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Real.log_le_log (by have := hx i; positivity : 0 < 1 + x i)
      (by have := hu i; linarith : 1 + x i ≤ 1 + L))
  simpa using hs

theorem matrix_logdet_upper {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ)
    (hB : B.PosDef) (L : ℝ)
    (hl : ∀ i, 1 ≤ hB.1.eigenvalues i)
    (hu : ∀ i, hB.1.eigenvalues i ≤ 1 + L) :
    Real.log B.det ≤ (N : ℝ) * Real.log (1 + L) := by
  rw [PallLean.Paper93.DeepMath.NFrame.log_det_posDef_eq_sum_log_eigenvalues B hB]
  have h := spectral_log_upper (fun i => hB.1.eigenvalues i - 1) L
    (fun i => sub_nonneg.mpr (hl i)) (fun i => by have := hu i; linarith)
  simpa only [show ∀ a : ℝ, 1 + (a - 1) = a from fun a => by ring] using h

end OverlapBudgetCeiling

#print axioms OverlapBudgetCeiling.normalized_mass_le_dimension
#print axioms OverlapBudgetCeiling.matrix_logdet_upper
