import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermutation

/-!
# Inverse of a decorated permutation

This file defines the inverse of a decorated permutation: invert the underlying
permutation while keeping the decoration map. We then prove a few structural
properties:

* The inverse of the identity decorated permutation is itself.
* The inverse of the negated-identity decorated permutation is itself.
* Inverting twice gives back the original underlying permutation.
* The decoration is preserved under inversion.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The inverse of a decorated permutation: invert the permutation, keep the
    decoration map. -/
def DecoratedPermutation.inverse {n : ℕ} (σ : DecoratedPermutation n) :
    DecoratedPermutation n where
  perm := σ.perm.symm
  decoration := σ.decoration

/-- The inverse of the identity is the identity. -/
theorem DecoratedPermutation.inverse_id (n : ℕ) :
    (DecoratedPermutation.id n).inverse = DecoratedPermutation.id n := by
  unfold DecoratedPermutation.inverse DecoratedPermutation.id
  refine congrArg₂ DecoratedPermutation.mk ?_ rfl
  exact Equiv.refl_symm

/-- Inverting twice gives back the original permutation (up to decoration equality). -/
theorem DecoratedPermutation.inverse_inverse_perm {n : ℕ} (σ : DecoratedPermutation n) :
    σ.inverse.inverse.perm = σ.perm := by
  unfold DecoratedPermutation.inverse
  exact σ.perm.symm_symm

/-- The decoration is preserved under inversion. -/
theorem DecoratedPermutation.inverse_decoration {n : ℕ} (σ : DecoratedPermutation n)
    (i : Fin n) : σ.inverse.decoration i = σ.decoration i := rfl

/-- The negated-id decorated permutation has the negated-id as its inverse. -/
theorem DecoratedPermutation.inverse_neg_id (n : ℕ) :
    (DecoratedPermutation.neg_id n).inverse = DecoratedPermutation.neg_id n := by
  unfold DecoratedPermutation.inverse DecoratedPermutation.neg_id
  refine congrArg₂ DecoratedPermutation.mk ?_ rfl
  exact Equiv.refl_symm

end PallLean.Paper93.DeepMath.PathB.Positroid
