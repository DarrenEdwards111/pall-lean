import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Pi

namespace PallLean.Paper93.DeepMath.GadgetRank

/-- `(α • I).mulVec v = α • v`. -/
theorem smul_one_mulVec {n : ℕ} (α : ℝ) (v : Fin n → ℝ) :
    (α • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec v = α • v := by
  rw [Matrix.smul_mulVec]
  ext i
  simp

/-- Quadratic form of `α • I` equals `α · ∑ v_i²`. -/
theorem smul_one_quadForm {n : ℕ} (α : ℝ) (v : Fin n → ℝ) :
    ∑ i, v i * ((α • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec v i) = α * ∑ i, v i * v i := by
  rw [smul_one_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

end PallLean.Paper93.DeepMath.GadgetRank
