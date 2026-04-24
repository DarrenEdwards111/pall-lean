import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

namespace PallLean.Paper93.DeepMath

theorem sum_const_fin (n k : ℕ) : ∑ _ : Fin n, k = n * k := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]

end PallLean.Paper93.DeepMath
