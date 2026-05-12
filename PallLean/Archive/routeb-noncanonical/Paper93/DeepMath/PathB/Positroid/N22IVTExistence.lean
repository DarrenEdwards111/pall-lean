import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem alpha_alpha_plus_22_continuous : Continuous (fun α : ℝ => α * (α + 22)^21) := by
  apply Continuous.mul
  · exact continuous_id
  · exact (continuous_id.add continuous_const).pow 21

theorem exists_alpha_n22_det_one_le : ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α * (α + 22)^21 = 1 := by
  have h_cont := alpha_alpha_plus_22_continuous
  have h0 : (fun α : ℝ => α * (α + 22)^21) 0 = 0 := by simp
  have h_ge_one : (1 : ℝ) ≤ (fun α : ℝ => α * (α + 22)^21) 1 := by
    show (1 : ℝ) ≤ 1 * (1 + 22)^21
    have h22 : (1 : ℝ) ≤ 1 + 22 := by norm_num
    have := one_le_pow₀ h22 (n := 21)
    linarith
  have h_ivt := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) h_cont.continuousOn
  have h_in : (1 : ℝ) ∈ Set.Icc ((fun α : ℝ => α * (α + 22)^21) 0) ((fun α : ℝ => α * (α + 22)^21) 1) := by
    rw [h0]; exact ⟨by norm_num, h_ge_one⟩
  obtain ⟨α, hα_mem, hα_eq⟩ := h_ivt h_in
  refine ⟨α, ?_, hα_mem.2, hα_eq⟩
  by_contra h_neg; push_neg at h_neg
  have : α = 0 := le_antisymm h_neg hα_mem.1
  rw [this] at hα_eq
  have : (0 : ℝ) * (0 + 22)^21 = 0 := by ring
  linarith

theorem n22_ivt_existence : ∃ α ∈ Set.Ioo (0:ℝ) 1, α * (α + 22)^21 = 1 := by
  obtain ⟨α, hα_pos, hα_le, hα_eq⟩ := exists_alpha_n22_det_one_le
  -- We need α < 1 strictly. If α = 1 then 1 * 23^21 = 23^21 ≠ 1.
  rcases lt_or_eq_of_le hα_le with hα_lt | hα_one
  · exact ⟨α, ⟨hα_pos, hα_lt⟩, hα_eq⟩
  · exfalso
    -- hα_one : α = 1, so hα_eq becomes 1 * (1 + 22)^21 = 1, i.e. 23^21 = 1
    rw [hα_one] at hα_eq
    have h23 : (1 : ℝ) * (1 + 22)^21 = (23 : ℝ)^21 := by ring
    rw [h23] at hα_eq
    -- hα_eq : (23 : ℝ)^21 = 1, but 23^21 > 1
    have h2 : (2 : ℝ) ≤ 23 := by norm_num
    have h2_le : (2 : ℝ)^21 ≤ (23 : ℝ)^21 :=
      pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h2 21
    have h2_gt : (1 : ℝ) < (2 : ℝ)^21 := by norm_num
    linarith

end PallLean.Paper93.DeepMath.PathB.Positroid
