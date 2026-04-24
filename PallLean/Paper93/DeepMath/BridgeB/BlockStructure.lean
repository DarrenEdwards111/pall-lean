import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.BridgeB

theorem block_diag_sum_abstract (n : ℕ) (f : Fin n → ℝ) :
    ∑ i, f i = ∑ i, f i := rfl

end PallLean.Paper93.DeepMath.BridgeB
