import PallLean.Paper93.DeepMath.NFrame.LogDetEigenvalues
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace BoundedOverlapLogDet

/-- Quantitative lower estimate that allows overlap instead of assuming additivity. -/
theorem scalar_lower {x L : ℝ} (hx : 0 ≤ x) (hL : 0 ≤ L) (hxL : x ≤ L) :
    x / (1+L) ≤ Real.log (1+x) := by
  have hp : 0 < 1+x := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hp
  have he : 1 - (1+x)⁻¹ = x / (1+x) := by field_simp; ring
  rw [he] at h
  exact (div_le_div_of_nonneg_left hx hp (by linarith : 1+x ≤ 1+L)).trans h

/-- Eigenvalue-mass lower bound with a uniform upper spectral bound. -/
theorem spectral_lower {N : ℕ} (x : Fin N → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hx : ∀ i, 0 ≤ x i) (hupper : ∀ i, x i ≤ L) :
    (∑ i, x i) / (1+L) ≤ ∑ i, Real.log (1+x i) := by
  rw [Finset.sum_div]
  exact Finset.sum_le_sum (fun i _ => scalar_lower (hx i) hL (hupper i))

/-- For PSD local matrices, trace additivity can supply this mass estimate.
The mass estimate and overlap bound still need proofs for the intended SAT map. -/
theorem rank_budget_lower {N : ℕ} (x : Fin N → ℝ) (L mu R : ℝ)
    (hL : 0 ≤ L) (hx : ∀ i, 0 ≤ x i) (hupper : ∀ i, x i ≤ L)
    (hmass : mu * R ≤ ∑ i, x i) :
    (mu / (1+L)) * R ≤ ∑ i, Real.log (1+x i) := by
  calc
    (mu / (1+L)) * R = (mu * R) / (1+L) := by ring
    _ ≤ (∑ i, x i) / (1+L) := div_le_div_of_nonneg_right hmass (by positivity)
    _ ≤ _ := spectral_lower x L hL hx hupper

/-- Matrix form for the shifted matrix B itself, using only the narrow spectral import. -/
theorem matrix_logdet_lower {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ)
    (hB : B.PosDef) (L mu R : ℝ) (hL : 0 ≤ L)
    (hlower : ∀ i, 1 ≤ hB.1.eigenvalues i)
    (hupper : ∀ i, hB.1.eigenvalues i ≤ 1+L)
    (hmass : mu * R ≤ B.trace - (N : ℝ)) :
    (mu / (1+L)) * R ≤ Real.log B.det := by
  rw [PallLean.Paper93.DeepMath.NFrame.log_det_posDef_eq_sum_log_eigenvalues B hB]
  have h := rank_budget_lower (fun i => hB.1.eigenvalues i - 1) L mu R hL
    (fun i => sub_nonneg.mpr (hlower i))
    (fun i => by have := hupper i; linarith)
    (by simpa [Finset.sum_sub_distrib, hB.1.trace_eq_sum_eigenvalues] using hmass)
  simpa only [show ∀ x : ℝ, 1 + (x - 1) = x from fun x => by ring] using h

end BoundedOverlapLogDet
#print axioms BoundedOverlapLogDet.rank_budget_lower

#print axioms BoundedOverlapLogDet.matrix_logdet_lower
