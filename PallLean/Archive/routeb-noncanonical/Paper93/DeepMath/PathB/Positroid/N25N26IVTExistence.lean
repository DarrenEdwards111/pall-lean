import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-! ### n = 25 -/

theorem alpha_alpha_plus_25_continuous : Continuous (fun α : ℝ => α * (α + 25)^24) := by
  apply Continuous.mul
  · exact continuous_id
  · exact (continuous_id.add continuous_const).pow 24

theorem n25_ivt_existence : ∃ α ∈ Set.Ioo (0:ℝ) 1, α * (α + 25)^24 = 1 := by
  have h_cont := alpha_alpha_plus_25_continuous
  have h0 : (fun α : ℝ => α * (α + 25)^24) 0 = 0 := by simp
  have h_ge_one : (1 : ℝ) ≤ (fun α : ℝ => α * (α + 25)^24) 1 := by
    show (1 : ℝ) ≤ 1 * (1 + 25)^24
    have h26 : (1 : ℝ) ≤ 1 + 25 := by norm_num
    have := one_le_pow₀ h26 (n := 24)
    linarith
  have h_ivt := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) h_cont.continuousOn
  have h_in : (1 : ℝ) ∈ Set.Icc ((fun α : ℝ => α * (α + 25)^24) 0)
      ((fun α : ℝ => α * (α + 25)^24) 1) := by
    rw [h0]; exact ⟨by norm_num, h_ge_one⟩
  obtain ⟨α, hα_mem, hα_eq⟩ := h_ivt h_in
  refine ⟨α, ⟨?_, ?_⟩, hα_eq⟩
  · -- 0 < α: rule out α = 0 since equation gives 0 ≠ 1
    by_contra h_neg; push_neg at h_neg
    have hα0 : α = 0 := le_antisymm h_neg hα_mem.1
    rw [hα0] at hα_eq
    have : (0 : ℝ) * (0 + 25)^24 = 0 := by ring
    linarith
  · -- α < 1: rule out α = 1 since (1+25)^24 ≥ 2 > 1, so 1*(1+25)^24 > 1 ≠ 1
    rcases lt_or_eq_of_le hα_mem.2 with hlt | heq
    · exact hlt
    · exfalso
      rw [heq] at hα_eq
      -- hα_eq : 1 * (1 + 25)^24 = 1
      have h2 : (2 : ℝ) ≤ 1 + 25 := by norm_num
      have hpow : (2 : ℝ)^24 ≤ (1 + 25)^24 :=
        pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h2 24
      have h2pow : (2 : ℝ) ≤ (2 : ℝ)^24 := by
        have h12 : (1 : ℝ) ≤ 2 := by norm_num
        have h23 : (1 : ℝ) ≤ (2:ℝ)^23 := one_le_pow₀ h12 (n := 23)
        have hsq : (2:ℝ)^24 = 2 * (2:ℝ)^23 := by ring
        linarith
      have : (1 + 25 : ℝ)^24 = 1 := by linarith [hα_eq]
      linarith

/-! ### n = 26 -/

theorem alpha_alpha_plus_26_continuous : Continuous (fun α : ℝ => α * (α + 26)^25) := by
  apply Continuous.mul
  · exact continuous_id
  · exact (continuous_id.add continuous_const).pow 25

theorem n26_ivt_existence : ∃ α ∈ Set.Ioo (0:ℝ) 1, α * (α + 26)^25 = 1 := by
  have h_cont := alpha_alpha_plus_26_continuous
  have h0 : (fun α : ℝ => α * (α + 26)^25) 0 = 0 := by simp
  have h_ge_one : (1 : ℝ) ≤ (fun α : ℝ => α * (α + 26)^25) 1 := by
    show (1 : ℝ) ≤ 1 * (1 + 26)^25
    have h27 : (1 : ℝ) ≤ 1 + 26 := by norm_num
    have := one_le_pow₀ h27 (n := 25)
    linarith
  have h_ivt := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) h_cont.continuousOn
  have h_in : (1 : ℝ) ∈ Set.Icc ((fun α : ℝ => α * (α + 26)^25) 0)
      ((fun α : ℝ => α * (α + 26)^25) 1) := by
    rw [h0]; exact ⟨by norm_num, h_ge_one⟩
  obtain ⟨α, hα_mem, hα_eq⟩ := h_ivt h_in
  refine ⟨α, ⟨?_, ?_⟩, hα_eq⟩
  · by_contra h_neg; push_neg at h_neg
    have hα0 : α = 0 := le_antisymm h_neg hα_mem.1
    rw [hα0] at hα_eq
    have : (0 : ℝ) * (0 + 26)^25 = 0 := by ring
    linarith
  · rcases lt_or_eq_of_le hα_mem.2 with hlt | heq
    · exact hlt
    · exfalso
      rw [heq] at hα_eq
      have h2 : (2 : ℝ) ≤ 1 + 26 := by norm_num
      have hpow : (2 : ℝ)^25 ≤ (1 + 26)^25 :=
        pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h2 25
      have h2pow : (2 : ℝ) ≤ (2 : ℝ)^25 := by
        have h12 : (1 : ℝ) ≤ 2 := by norm_num
        have h24 : (1 : ℝ) ≤ (2:ℝ)^24 := one_le_pow₀ h12 (n := 24)
        have hsq : (2:ℝ)^25 = 2 * (2:ℝ)^24 := by ring
        linarith
      have : (1 + 26 : ℝ)^25 = 1 := by linarith [hα_eq]
      linarith

end PallLean.Paper93.DeepMath.PathB.Positroid
