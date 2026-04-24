import PallLean.Paper93.DeepMath.GadgetRank.IdentityQuad
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.GadgetRank

/-- For `c > 0` and `R > 0`, there exists a vector `Φ` with `∑ φᵢ² ≥ R/c`. -/
theorem exists_large_sum_sq (n : ℕ) (hn : 1 ≤ n) (R : ℝ) :
    ∃ phi : Fin n → ℝ, R ≤ ∑ i, phi i * phi i := by
  -- Take phi = constant vector of size sqrt(R/n + 1); sum = n · (R/n + 1) = R + n ≥ R.
  by_cases hR : R ≤ 0
  · refine ⟨0, ?_⟩
    have h0 : (0 : ℝ) ≤ ∑ i, (0 : Fin n → ℝ) i * (0 : Fin n → ℝ) i := sum_sq_nonneg _
    linarith
  · push_neg at hR
    -- Take phi i = Real.sqrt(R/n) + 1 for every i; then ∑ φᵢ² = n·c² ≥ R.
    have h_n_pos : 0 < (n : ℝ) := by exact_mod_cast hn
    let c := Real.sqrt (R / (n : ℝ)) + 1
    refine ⟨fun _ => c, ?_⟩
    have h_div_nn : 0 ≤ R / (n : ℝ) := div_nonneg (le_of_lt hR) (le_of_lt h_n_pos)
    have h_sqrt_nn : 0 ≤ Real.sqrt (R / (n : ℝ)) := Real.sqrt_nonneg _
    have h_sqrt_sq : Real.sqrt (R / (n : ℝ)) ^ 2 = R / (n : ℝ) := Real.sq_sqrt h_div_nn
    have h_c_sq_ge : (R / (n : ℝ)) ≤ c * c := by
      have hexpand : c * c =
          Real.sqrt (R / (n : ℝ)) ^ 2 + 2 * Real.sqrt (R / (n : ℝ)) + 1 := by
        show (Real.sqrt (R / (n : ℝ)) + 1) * (Real.sqrt (R / (n : ℝ)) + 1) = _
        ring
      rw [hexpand, h_sqrt_sq]
      nlinarith [h_sqrt_nn]
    have h_sum : ∑ _i : Fin n, c * c = (n : ℝ) * (c * c) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h_R_le : (R : ℝ) ≤ (n : ℝ) * (R / (n : ℝ)) := by
      rw [mul_div_assoc', mul_comm, mul_div_assoc]
      rw [div_self (ne_of_gt h_n_pos), mul_one]
    calc R ≤ (n : ℝ) * (R / (n : ℝ)) := h_R_le
      _ ≤ (n : ℝ) * (c * c) := by
          apply mul_le_mul_of_nonneg_left h_c_sq_ge (le_of_lt h_n_pos)
      _ = ∑ _i : Fin n, c * c := h_sum.symm

/-- For n ≥ 1, there exists a vector Φ with `∑ φᵢ² ≥ 1` (take Φ = Pi.single 0 1). -/
theorem exists_unit_sum_sq (n : ℕ) (hn : 1 ≤ n) :
    ∃ phi : Fin n → ℝ, 1 ≤ ∑ i, phi i * phi i := by
  have h_pos : 0 < n := hn
  let i0 : Fin n := ⟨0, h_pos⟩
  refine ⟨fun i => if i = i0 then 1 else 0, ?_⟩
  have hrewrite : ∀ i : Fin n, (if i = i0 then (1:ℝ) else 0) * (if i = i0 then 1 else 0) =
          if i = i0 then 1 else 0 := by
    intro i; by_cases h : i = i0 <;> simp [h]
  simp_rw [hrewrite]
  rw [Finset.sum_ite_eq' Finset.univ i0]
  simp

end PallLean.Paper93.DeepMath.NFrame
