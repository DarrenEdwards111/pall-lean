import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace PallLean.Paper93.DeepMath.GadgetRank

/-- Quadratic form is additive in the matrix: `vᵀ (M + N) v = vᵀ M v + vᵀ N v`. -/
theorem quadForm_add {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    ∑ i, v i * ((M + N).mulVec v i) =
      (∑ i, v i * (M.mulVec v i)) + (∑ i, v i * (N.mulVec v i)) := by
  rw [Matrix.add_mulVec]
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros i _
  ring

end PallLean.Paper93.DeepMath.GadgetRank
