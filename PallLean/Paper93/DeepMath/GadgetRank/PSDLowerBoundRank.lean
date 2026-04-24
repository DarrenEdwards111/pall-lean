import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Positivity

namespace PallLean.Paper93.DeepMath.GadgetRank

/-- If a symmetric real matrix is ≥ α · I (i.e., `∀ v, vᵀ M v ≥ α · vᵀ v`) with α > 0,
    AND v ≠ 0, then `vᵀ M v > 0`. In particular M is not zero. -/
theorem posDef_of_uniform_lb {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (α : ℝ) (hα : 0 < α)
    (hM : ∀ v : Fin n → ℝ, α * (∑ i, v i * v i) ≤ ∑ i, v i * (M.mulVec v i))
    (v : Fin n → ℝ) (hv : v ≠ 0) :
    0 < ∑ i, v i * (M.mulVec v i) := by
  have h_pos : 0 < ∑ i, v i * v i := by
    -- v ≠ 0 ⇒ some component v k ≠ 0 ⇒ sum of squares > 0
    rcases Function.ne_iff.mp hv with ⟨k, hk⟩
    apply Finset.sum_pos' (fun i _ => mul_self_nonneg (v i))
    refine ⟨k, Finset.mem_univ k, ?_⟩
    have hk' : v k ≠ 0 := by
      intro h
      exact hk (by simp [h])
    exact (mul_self_pos).mpr hk'
  calc 0 < α * (∑ i, v i * v i) := by positivity
    _ ≤ ∑ i, v i * (M.mulVec v i) := hM v

end PallLean.Paper93.DeepMath.GadgetRank
