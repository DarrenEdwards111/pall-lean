import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetSumZero
import PallLean.Paper93.DeepMath.GadgetRank.IdentityQuad
import Mathlib.Tactic.Linarith

namespace PallLean.Paper93.DeepMath.GadgetRank

/-- Strict positivity of the compiled gadget quadratic form on nonzero sum-zero vectors:
    for `α ≥ 0`, `n ≥ 1`, and `v ≠ 0` with `∑ vᵢ = 0`,
    `0 < ∑ vᵢ · (compiledGadget α n · v) i`. -/
theorem compiledGadget_quad_pos_on_sumZero (α : ℝ) (n : ℕ)
    (hα : 0 ≤ α) (hn : 1 ≤ n)
    (v : Fin n → ℝ) (hv_sum : ∑ i, v i = 0) (hv_ne : v ≠ 0) :
    0 < ∑ i, v i * ((compiledGadget α n).mulVec v i) := by
  rw [compiledGadget_quadForm_sumZero α n v hv_sum]
  have h_sum_pos : 0 < ∑ i, v i * v i := sum_sq_pos_of_ne_zero v hv_ne
  have h_coef_pos : (0 : ℝ) < α + n := by
    have hn_cast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact mul_pos h_coef_pos h_sum_pos

end PallLean.Paper93.DeepMath.GadgetRank
