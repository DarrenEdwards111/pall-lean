import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem alpha_alpha_plus_9_octic_continuous :
    Continuous (fun α : ℝ => α * (α + 9)^8) := by
  apply Continuous.mul
  · exact continuous_id
  · exact (continuous_id.add continuous_const).pow 8

theorem exists_alpha_n9_det_one :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 9)^8 = 1 := by
  have h_cont := alpha_alpha_plus_9_octic_continuous
  have h0 : (fun α : ℝ => α * (α + 9)^8) 0 = 0 := by simp
  have h1 : (fun α : ℝ => α * (α + 9)^8) 1 = 100000000 := by norm_num
  have h_ivt := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) h_cont.continuousOn
  have h_in : (1 : ℝ) ∈ Set.Icc ((fun α : ℝ => α * (α + 9)^8) 0) ((fun α : ℝ => α * (α + 9)^8) 1) := by
    rw [h0, h1]; exact ⟨by norm_num, by norm_num⟩
  obtain ⟨α, hα_mem, hα_eq⟩ := h_ivt h_in
  refine ⟨α, ?_, ?_, hα_eq⟩
  · by_contra h_neg; push_neg at h_neg
    have h_eq_0 : α = 0 := le_antisymm h_neg hα_mem.1
    rw [h_eq_0] at hα_eq; norm_num at hα_eq
  · by_contra h_neg; push_neg at h_neg
    have h_eq_1 : α = 1 := le_antisymm hα_mem.2 h_neg
    rw [h_eq_1] at hα_eq; norm_num at hα_eq

end PallLean.Paper93.DeepMath.PathB.Positroid
