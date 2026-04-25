import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem alpha_alpha_plus_17_continuous : Continuous (fun α : ℝ => α * (α + 17)^16) := by
  apply Continuous.mul
  · exact continuous_id
  · exact (continuous_id.add continuous_const).pow 16

theorem exists_alpha_n17_det_one : ∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 17)^16 = 1 := by
  have h_cont := alpha_alpha_plus_17_continuous
  have h0 : (fun α : ℝ => α * (α + 17)^16) 0 = 0 := by simp
  have h1 : (fun α : ℝ => α * (α + 17)^16) 1 = 121439531096594251776 := by norm_num
  have h_ivt := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) h_cont.continuousOn
  have h_in : (1 : ℝ) ∈ Set.Icc ((fun α : ℝ => α * (α + 17)^16) 0) ((fun α : ℝ => α * (α + 17)^16) 1) := by
    rw [h0, h1]; exact ⟨by norm_num, by norm_num⟩
  obtain ⟨α, hα_mem, hα_eq⟩ := h_ivt h_in
  refine ⟨α, ?_, ?_, hα_eq⟩
  · by_contra h_neg; push_neg at h_neg
    have : α = 0 := le_antisymm h_neg hα_mem.1
    rw [this] at hα_eq; norm_num at hα_eq
  · by_contra h_neg; push_neg at h_neg
    have : α = 1 := le_antisymm hα_mem.2 h_neg
    rw [this] at hα_eq; norm_num at hα_eq

end PallLean.Paper93.DeepMath.PathB.Positroid
