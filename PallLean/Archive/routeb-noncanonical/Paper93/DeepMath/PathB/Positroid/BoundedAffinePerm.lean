import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Order.Basic

/-!
# Bounded affine permutations on ℤ (positroid building block)

A *bounded affine permutation* of order `n` is a bijection `f : ℤ → ℤ` such that
* `f(i + n) = f(i) + n` for all `i ∈ ℤ` (n-periodic shift property), and
* `i ≤ f(i) ≤ i + n` for all `i ∈ ℤ` (boundedness).

Such permutations index positroid cells in the Grassmannian `Gr(k, n)` and form
the combinatorial backbone of positroid stratification.

This file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- A **bounded affine permutation** of order `n`: a bijection `ℤ ≃ ℤ` that is
    n-periodic-equivariant and bounded by `[i, i+n]`. -/
structure BoundedAffinePerm (n : ℕ) where
  /-- The underlying bijection. -/
  toFun : ℤ ≃ ℤ
  /-- n-periodic shift property: `f(i + n) = f(i) + n`. -/
  shift_property : ∀ i : ℤ, toFun (i + n) = toFun i + n
  /-- Boundedness from below: `i ≤ f(i)`. -/
  lower_bound : ∀ i : ℤ, i ≤ toFun i
  /-- Boundedness from above: `f(i) ≤ i + n`. -/
  upper_bound : ∀ i : ℤ, toFun i ≤ i + n

/-- The identity bounded affine permutation (`f = id`). -/
def BoundedAffinePerm.id (n : ℕ) : BoundedAffinePerm n where
  toFun := Equiv.refl ℤ
  shift_property := fun _ => rfl
  lower_bound := fun i => le_refl i
  upper_bound := fun i => by
    show i ≤ i + (n : ℤ)
    exact Int.le_add_of_nonneg_right (Int.natCast_nonneg n)

/-- The identity bounded affine permutation has the expected underlying bijection. -/
theorem BoundedAffinePerm.id_toFun (n : ℕ) :
    (BoundedAffinePerm.id n).toFun = Equiv.refl ℤ := rfl

/-- For the identity bounded affine permutation, `f(i) = i`. -/
theorem BoundedAffinePerm.id_apply (n : ℕ) (i : ℤ) :
    (BoundedAffinePerm.id n).toFun i = i := rfl

/-- Shift property of the identity: `i + n` is shifted to itself + n (trivially). -/
theorem BoundedAffinePerm.id_shift (n : ℕ) (i : ℤ) :
    (BoundedAffinePerm.id n).toFun (i + n) = (BoundedAffinePerm.id n).toFun i + n :=
  (BoundedAffinePerm.id n).shift_property i

end PallLean.Paper93.DeepMath.PathB.Positroid
