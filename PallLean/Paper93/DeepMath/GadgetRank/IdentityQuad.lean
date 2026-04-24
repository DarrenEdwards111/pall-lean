import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Positivity

namespace PallLean.Paper93.DeepMath.GadgetRank

/-- Identity matrix's mulVec is the identity function. -/
theorem one_mulVec {n : ℕ} (v : Fin n → ℝ) :
    (1 : Matrix (Fin n) (Fin n) ℝ).mulVec v = v := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Finset.sum_ite_eq]

/-- Identity-matrix quadratic form equals sum of squares. -/
theorem one_quadForm {n : ℕ} (v : Fin n → ℝ) :
    ∑ i, v i * ((1 : Matrix (Fin n) (Fin n) ℝ).mulVec v i) = ∑ i, v i * v i := by
  rw [one_mulVec]

/-- Sum of squares is nonneg. -/
theorem sum_sq_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ ∑ i, v i * v i :=
  Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)

/-- A nonzero vector has strictly positive sum of squares. -/
theorem sum_sq_pos_of_ne_zero {n : ℕ} (v : Fin n → ℝ) (hv : v ≠ 0) :
    0 < ∑ i, v i * v i := by
  rcases Function.ne_iff.mp hv with ⟨k, hk⟩
  apply Finset.sum_pos' (fun i _ => mul_self_nonneg (v i))
  exact ⟨k, Finset.mem_univ k, by
    have : v k ≠ 0 := hk
    exact mul_self_pos.mpr this⟩

end PallLean.Paper93.DeepMath.GadgetRank
