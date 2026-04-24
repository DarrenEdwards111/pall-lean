import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.BridgeB

theorem logDet_block_sum_nonneg (n : ℕ) (vals : Fin n → ℝ)
    (h : ∀ i, 0 ≤ vals i) : 0 ≤ ∑ i, vals i :=
  Finset.sum_nonneg (fun i _ => h i)
