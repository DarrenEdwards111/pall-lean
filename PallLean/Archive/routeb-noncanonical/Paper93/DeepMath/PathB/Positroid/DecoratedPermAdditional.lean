import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermutation
import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermComposition
import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermInverse
import PallLean.Paper93.DeepMath.PathB.Positroid.DecorationSign
import PallLean.Paper93.DeepMath.PathB.Positroid.DecorationProduct
import Mathlib.Logic.Equiv.Basic

/-!
# Additional structural lemmas for decorated permutations

This file collects a handful of additional structural identities for the
`DecoratedPermutation` algebra: full structure-level identity and inverse
laws (not merely on the underlying `perm` component), and their
interactions with the decoration sign product.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- Identity composed with itself is identity (full structural equality). -/
theorem DecoratedPermutation.id_compose_id_full (n : ℕ) :
    (DecoratedPermutation.id n).compose (DecoratedPermutation.id n) =
    DecoratedPermutation.id n := by
  unfold DecoratedPermutation.compose DecoratedPermutation.id
  refine congrArg₂ DecoratedPermutation.mk ?_ rfl
  exact Equiv.trans_refl _

/-- Composition with identity on the right preserves the whole decorated
    permutation, not just its `perm` component. -/
theorem DecoratedPermutation.compose_id_right_full {n : ℕ}
    (σ : DecoratedPermutation n) :
    σ.compose (DecoratedPermutation.id n) = σ := by
  cases σ with
  | mk p d =>
    unfold DecoratedPermutation.compose DecoratedPermutation.id
    refine congrArg₂ DecoratedPermutation.mk ?_ rfl
    exact Equiv.trans_refl _

/-- Inverting twice gives back the original decorated permutation
    (full structural equality, not just on `perm`). -/
theorem DecoratedPermutation.inverse_inverse_full {n : ℕ}
    (σ : DecoratedPermutation n) :
    σ.inverse.inverse = σ := by
  cases σ with
  | mk p d =>
    unfold DecoratedPermutation.inverse
    refine congrArg₂ DecoratedPermutation.mk ?_ rfl
    exact p.symm_symm

/-- The inverse of the identity has sign-product 1. -/
theorem DecoratedPermutation.inverse_id_signProduct (n : ℕ) :
    (DecoratedPermutation.id n).inverse.signProduct = 1 := by
  rw [DecoratedPermutation.inverse_id]
  exact DecoratedPermutation.id_signProduct n

/-- Composition keeps the decoration of the first argument, hence the sign
    product is unchanged when composing with identity on the right. -/
theorem DecoratedPermutation.compose_id_right_signProduct {n : ℕ}
    (σ : DecoratedPermutation n) :
    (σ.compose (DecoratedPermutation.id n)).signProduct = σ.signProduct := by
  rw [DecoratedPermutation.compose_id_right_full]

/-- The inverse preserves the sign product (since `inverse` keeps the
    decoration map). -/
theorem DecoratedPermutation.inverse_signProduct {n : ℕ}
    (σ : DecoratedPermutation n) :
    σ.inverse.signProduct = σ.signProduct := by
  unfold DecoratedPermutation.signProduct DecoratedPermutation.inverse
  rfl

end PallLean.Paper93.DeepMath.PathB.Positroid
