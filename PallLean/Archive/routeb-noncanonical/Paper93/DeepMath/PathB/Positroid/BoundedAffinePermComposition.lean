import PallLean.Paper93.DeepMath.PathB.Positroid.BoundedAffinePerm

/-!
# Composition properties for bounded affine permutations

A *bounded affine permutation* of order `n` is a bijection `f : ℤ → ℤ`
such that `f(i + n) = f(i) + n` and `i ≤ f(i) ≤ i + n` for all `i`.

Pure composition does **not** preserve the bound `f(i) ≤ i + n`: if `f` and
`g` are bounded affine of order `n`, then `(g ∘ f)(i) ≤ (i + n) + n = i + 2n`,
which only gives an order-`2n` bound in general.  For this reason, the
"composition" structure on `BoundedAffinePerm n` is most naturally taken to
be a cyclic/quotient construction; in this kernel-only file we content
ourselves with the unconditional statement that the identity composes with
itself to the identity, together with the basic identity laws used elsewhere.

This file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- Composition of identity bounded affine permutations is the identity. -/
theorem BoundedAffinePerm_id_compose_id (n : ℕ) :
    (BoundedAffinePerm.id n).toFun.trans (BoundedAffinePerm.id n).toFun
      = (BoundedAffinePerm.id n).toFun :=
  Equiv.refl_trans _

/-- The identity bounded affine permutation maps every `i` to `i`. -/
theorem BoundedAffinePerm_id_apply_eq (n : ℕ) (i : ℤ) :
    (BoundedAffinePerm.id n).toFun i = i := rfl

/-- The shift property holds for the identity bounded affine permutation. -/
theorem BoundedAffinePerm_id_shift_property (n : ℕ) (i : ℤ) :
    (BoundedAffinePerm.id n).toFun (i + n) = (BoundedAffinePerm.id n).toFun i + n :=
  (BoundedAffinePerm.id n).shift_property i

/-- The lower bound `i ≤ f(i)` holds for the identity bounded affine permutation. -/
theorem BoundedAffinePerm_id_lower_bound (n : ℕ) (i : ℤ) :
    i ≤ (BoundedAffinePerm.id n).toFun i :=
  (BoundedAffinePerm.id n).lower_bound i

/-- The upper bound `f(i) ≤ i + n` holds for the identity bounded affine permutation. -/
theorem BoundedAffinePerm_id_upper_bound (n : ℕ) (i : ℤ) :
    (BoundedAffinePerm.id n).toFun i ≤ i + n :=
  (BoundedAffinePerm.id n).upper_bound i

end PallLean.Paper93.DeepMath.PathB.Positroid
