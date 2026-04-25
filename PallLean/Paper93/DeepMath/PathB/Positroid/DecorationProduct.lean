import PallLean.Paper93.DeepMath.PathB.Positroid.DecorationSign
import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermutation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The product of decoration signs over all indices in a decorated permutation. -/
def DecoratedPermutation.signProduct {n : ℕ} (σ : DecoratedPermutation n) : ℝ :=
  ∏ i, (σ.decoration i).sign

/-- For the identity decorated permutation, signProduct = 1 (all positive). -/
theorem DecoratedPermutation.id_signProduct (n : ℕ) :
    (DecoratedPermutation.id n).signProduct = 1 := by
  unfold DecoratedPermutation.signProduct
  simp [DecoratedPermutation.id, Decoration.sign]

/-- For the negated-identity, signProduct = (-1)^n. -/
theorem DecoratedPermutation.neg_id_signProduct (n : ℕ) :
    (DecoratedPermutation.neg_id n).signProduct = (-1 : ℝ)^n := by
  unfold DecoratedPermutation.signProduct
  simp [DecoratedPermutation.neg_id, Decoration.sign, Finset.card_univ,
        Fintype.card_fin]

end PallLean.Paper93.DeepMath.PathB.Positroid
