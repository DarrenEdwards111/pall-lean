import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermutation
import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermInverse
import Mathlib.Logic.Equiv.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The inverse of the identity decorated permutation has identity perm. -/
theorem DecoratedPermutation.inverse_id_perm (n : ℕ) :
    (DecoratedPermutation.id n).inverse.perm = (DecoratedPermutation.id n).perm := by
  unfold DecoratedPermutation.inverse DecoratedPermutation.id
  exact Equiv.refl_symm

/-- Inverse of inverse on perm equals original. -/
theorem DecoratedPermutation.inverse_inverse {n : ℕ} (σ : DecoratedPermutation n) :
    σ.inverse.inverse.perm = σ.perm :=
  DecoratedPermutation.inverse_inverse_perm σ

/-- The decoration of the inverse equals the decoration of the original. -/
theorem DecoratedPermutation.inverse_decoration_unchanged {n : ℕ} (σ : DecoratedPermutation n)
    (i : Fin n) :
    σ.inverse.decoration i = σ.decoration i :=
  DecoratedPermutation.inverse_decoration σ i

/-- Identity decorated permutation has positive decoration everywhere. -/
theorem DecoratedPermutation.id_decoration_positive (n : ℕ) (i : Fin n) :
    (DecoratedPermutation.id n).decoration i = Decoration.positive := rfl

/-- Negation-identity has negative decoration everywhere. -/
theorem DecoratedPermutation.neg_id_decoration_negative (n : ℕ) (i : Fin n) :
    (DecoratedPermutation.neg_id n).decoration i = Decoration.negative := rfl

end PallLean.Paper93.DeepMath.PathB.Positroid
