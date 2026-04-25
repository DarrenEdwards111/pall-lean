import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-! ### n = 23 -/

theorem alpha_alpha_plus_23_continuous : Continuous (fun α : ℝ => α * (α + 23)^22) := by
  apply Continuous.mul
  · exact continuous_id
  · exact (continuous_id.add continuous_const).pow 22

theorem n23_ivt_existence : ∃ α ∈ Set.Ioo (0:ℝ) 1, α * (α + 23)^22 = 1 := by
  have h_cont := alpha_alpha_plus_23_continuous
  have h0 : (fun α : ℝ => α * (α + 23)^22) 0 = 0 := by simp
  have h_ge_one : (1 : ℝ) ≤ (fun α : ℝ => α * (α + 23)^22) 1 := by
    show (1 : ℝ) ≤ 1 * (1 + 23)^22
    have h24 : (1 : ℝ) ≤ 1 + 23 := by norm_num
    have := one_le_pow₀ h24 (n := 22)
    linarith
  have h_ivt := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) h_cont.continuousOn
  have h_in : (1 : ℝ) ∈ Set.Icc ((fun α : ℝ => α * (α + 23)^22) 0)
      ((fun α : ℝ => α * (α + 23)^22) 1) := by
    rw [h0]; exact ⟨by norm_num, h_ge_one⟩
  obtain ⟨α, hα_mem, hα_eq⟩ := h_ivt h_in
  refine ⟨α, ⟨?_, ?_⟩, hα_eq⟩
  · -- 0 < α: rule out α = 0 since equation gives 0 ≠ 1
    by_contra h_neg; push_neg at h_neg
    have hα0 : α = 0 := le_antisymm h_neg hα_mem.1
    rw [hα0] at hα_eq
    have : (0 : ℝ) * (0 + 23)^22 = 0 := by ring
    linarith
  · -- α < 1: rule out α = 1 since (1+23)^22 ≥ 2 > 1, so 1*(1+23)^22 > 1 ≠ 1
    rcases lt_or_eq_of_le hα_mem.2 with hlt | heq
    · exact hlt
    · exfalso
      rw [heq] at hα_eq
      -- hα_eq : 1 * (1 + 23)^22 = 1
      have h2 : (2 : ℝ) ≤ 1 + 23 := by norm_num
      have hpow : (2 : ℝ)^22 ≤ (1 + 23)^22 :=
        pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h2 22
      have h2pow : (2 : ℝ) ≤ (2 : ℝ)^22 := by
        have h12 : (1 : ℝ) ≤ 2 := by norm_num
        have := one_le_pow₀ h12 (n := 22)
        -- 1 ≤ 2^22 ; we want 2 ≤ 2^22
        -- Use: 2^22 = 2 * 2^21
        have h21 : (1 : ℝ) ≤ (2:ℝ)^21 := one_le_pow₀ h12 (n := 21)
        have hsq : (2:ℝ)^22 = 2 * (2:ℝ)^21 := by ring
        linarith
      have : (1 + 23 : ℝ)^22 = 1 := by linarith [hα_eq]
      linarith

/-! ### n = 24 -/

theorem alpha_alpha_plus_24_continuous : Continuous (fun α : ℝ => α * (α + 24)^23) := by
  apply Continuous.mul
  · exact continuous_id
  · exact (continuous_id.add continuous_const).pow 23

theorem n24_ivt_existence : ∃ α ∈ Set.Ioo (0:ℝ) 1, α * (α + 24)^23 = 1 := by
  have h_cont := alpha_alpha_plus_24_continuous
  have h0 : (fun α : ℝ => α * (α + 24)^23) 0 = 0 := by simp
  have h_ge_one : (1 : ℝ) ≤ (fun α : ℝ => α * (α + 24)^23) 1 := by
    show (1 : ℝ) ≤ 1 * (1 + 24)^23
    have h25 : (1 : ℝ) ≤ 1 + 24 := by norm_num
    have := one_le_pow₀ h25 (n := 23)
    linarith
  have h_ivt := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) h_cont.continuousOn
  have h_in : (1 : ℝ) ∈ Set.Icc ((fun α : ℝ => α * (α + 24)^23) 0)
      ((fun α : ℝ => α * (α + 24)^23) 1) := by
    rw [h0]; exact ⟨by norm_num, h_ge_one⟩
  obtain ⟨α, hα_mem, hα_eq⟩ := h_ivt h_in
  refine ⟨α, ⟨?_, ?_⟩, hα_eq⟩
  · by_contra h_neg; push_neg at h_neg
    have hα0 : α = 0 := le_antisymm h_neg hα_mem.1
    rw [hα0] at hα_eq
    have : (0 : ℝ) * (0 + 24)^23 = 0 := by ring
    linarith
  · rcases lt_or_eq_of_le hα_mem.2 with hlt | heq
    · exact hlt
    · exfalso
      rw [heq] at hα_eq
      have h2 : (2 : ℝ) ≤ 1 + 24 := by norm_num
      have hpow : (2 : ℝ)^23 ≤ (1 + 24)^23 :=
        pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h2 23
      have h2pow : (2 : ℝ) ≤ (2 : ℝ)^23 := by
        have h12 : (1 : ℝ) ≤ 2 := by norm_num
        have h22 : (1 : ℝ) ≤ (2:ℝ)^22 := one_le_pow₀ h12 (n := 22)
        have hsq : (2:ℝ)^23 = 2 * (2:ℝ)^22 := by ring
        linarith
      have : (1 + 24 : ℝ)^23 = 1 := by linarith [hα_eq]
      linarith

end PallLean.Paper93.DeepMath.PathB.Positroid
