import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem alpha_alpha_plus_21_continuous : Continuous (fun α : ℝ => α * (α + 21)^20) := by
  apply Continuous.mul
  · exact continuous_id
  · exact (continuous_id.add continuous_const).pow 20

theorem exists_alpha_n21_det_one_le : ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α * (α + 21)^20 = 1 := by
  have h_cont := alpha_alpha_plus_21_continuous
  have h0 : (fun α : ℝ => α * (α + 21)^20) 0 = 0 := by simp
  have h_ge_one : (1 : ℝ) ≤ (fun α : ℝ => α * (α + 21)^20) 1 := by
    show (1 : ℝ) ≤ 1 * (1 + 21)^20
    have h21 : (1 : ℝ) ≤ 1 + 21 := by norm_num
    have := one_le_pow₀ h21 (n := 20)
    linarith
  have h_ivt := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) h_cont.continuousOn
  have h_in : (1 : ℝ) ∈ Set.Icc ((fun α : ℝ => α * (α + 21)^20) 0) ((fun α : ℝ => α * (α + 21)^20) 1) := by
    rw [h0]; exact ⟨by norm_num, h_ge_one⟩
  obtain ⟨α, hα_mem, hα_eq⟩ := h_ivt h_in
  refine ⟨α, ?_, hα_mem.2, hα_eq⟩
  by_contra h_neg; push_neg at h_neg
  have : α = 0 := le_antisymm h_neg hα_mem.1
  rw [this] at hα_eq
  have : (0 : ℝ) * (0 + 21)^20 = 0 := by ring
  linarith

end PallLean.Paper93.DeepMath.PathB.Positroid
