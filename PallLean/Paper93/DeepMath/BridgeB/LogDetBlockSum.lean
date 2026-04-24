import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Block

namespace PallLean.Paper93.DeepMath.BridgeB

theorem logDet_block_sum_nonneg (n : ℕ) (vals : Fin n → ℝ)
    (h : ∀ i, 0 ≤ vals i) : 0 ≤ ∑ i, vals i :=
  Finset.sum_nonneg (fun i _ => h i)

/-- `log ∘ det` of a block-diagonal matrix is the sum of `log ∘ det` over the blocks,
provided each block has strictly positive determinant. -/
theorem log_det_blockDiagonal_eq_sum_log_det
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (M : ι → Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ i, 0 < (M i).det) :
    Real.log ((Matrix.blockDiagonal M).det) = ∑ i, Real.log ((M i).det) := by
  rw [Matrix.det_blockDiagonal]
  exact Real.log_prod (s := Finset.univ) (f := fun i => (M i).det)
    (fun i _ => ne_of_gt (h i))

end PallLean.Paper93.DeepMath.BridgeB
