import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Decorated permutations (positroid index)

A **decorated permutation** of `[n]` is a permutation `σ ∈ Sₙ` together with a
"decoration" assigning to each fixed point of `σ` a sign `+1` or `-1`.
Decorated permutations are in bijection with bounded affine permutations of
order `n`, and index positroid cells of the totally nonnegative Grassmannian.

This file gives the basic kernel-only structure: a two-element decoration type,
the structure `DecoratedPermutation n`, two canonical instances (`id` and
`neg_id`), and a handful of definitional `rfl`-lemmas.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The decoration assigned to a fixed point: either positive (+1) or negative (-1). -/
inductive Decoration : Type
  | positive
  | negative
  deriving DecidableEq, Repr

/-- A **decorated permutation** of `[n]`: a bijection `σ : Fin n ≃ Fin n` with a
    decoration on each fixed point. -/
structure DecoratedPermutation (n : ℕ) where
  /-- The underlying permutation. -/
  perm : Fin n ≃ Fin n
  /-- The decoration: assigns a sign to every fixed point.
      For non-fixed points the value is unused. -/
  decoration : Fin n → Decoration

/-- The trivial decorated permutation: identity with all fixed points decorated as positive. -/
def DecoratedPermutation.id (n : ℕ) : DecoratedPermutation n where
  perm := Equiv.refl (Fin n)
  decoration := fun _ => Decoration.positive

/-- A second canonical decorated permutation: identity with all decorations negative. -/
def DecoratedPermutation.neg_id (n : ℕ) : DecoratedPermutation n where
  perm := Equiv.refl (Fin n)
  decoration := fun _ => Decoration.negative

/-- The underlying permutation of `id` is `Equiv.refl`. -/
theorem DecoratedPermutation.id_perm (n : ℕ) :
    (DecoratedPermutation.id n).perm = Equiv.refl (Fin n) := rfl

/-- The decoration of `id` is identically `positive`. -/
theorem DecoratedPermutation.id_decoration (n : ℕ) (i : Fin n) :
    (DecoratedPermutation.id n).decoration i = Decoration.positive := rfl

/-- For the identity decorated permutation, perm.toFun is the identity function. -/
theorem DecoratedPermutation.id_apply (n : ℕ) (i : Fin n) :
    (DecoratedPermutation.id n).perm i = i := rfl

/-- The negated-identity decorated permutation has all decorations negative. -/
theorem DecoratedPermutation.neg_id_decoration (n : ℕ) (i : Fin n) :
    (DecoratedPermutation.neg_id n).decoration i = Decoration.negative := rfl

/-- Decorations are decidably equal. -/
def Decoration.dec_eq (a b : Decoration) : Decidable (a = b) := by
  exact instDecidableEqDecoration a b

end PallLean.Paper93.DeepMath.PathB.Positroid
