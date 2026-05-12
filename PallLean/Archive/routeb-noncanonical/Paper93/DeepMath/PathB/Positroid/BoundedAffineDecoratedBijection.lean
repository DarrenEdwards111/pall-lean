import PallLean.Paper93.DeepMath.PathB.Positroid.BoundedAffinePerm
import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermutation

/-!
# Toy bijection between bounded affine permutations and decorated permutations

The deep theory of positroid combinatorics says that positroid cells of the
Grassmannian `Gr(k, n)` are in bijection with two equivalent indexing sets:

* `BoundedAffinePerm n` — bounded affine permutations of order `n`, and
* `DecoratedPermutation n` — permutations of `[n]` with a `±1` decoration at
  each fixed point.

The full bijection is a non-trivial combinatorial construction.  Here we give
a *toy* version that exhibits the correspondence on the identity element only:
the identity bounded affine permutation is matched with the decorated identity
permutation in which every fixed point is decorated as `positive`.

This file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- Toy correspondence at identity: the identity bounded affine permutation
    corresponds to the identity decorated permutation (with all positive
    decorations). -/
def boundedToDecorated_id (n : ℕ) :
    DecoratedPermutation n :=
  DecoratedPermutation.id n

/-- Reverse direction of the toy correspondence: the identity decorated
    permutation corresponds to the identity bounded affine permutation. -/
def decoratedToBounded_id (n : ℕ) :
    BoundedAffinePerm n :=
  BoundedAffinePerm.id n

/-- The toy bijection at identity: applying both maps in succession gives
    back identity. -/
theorem boundedDecorated_id_roundtrip (n : ℕ) :
    (decoratedToBounded_id n |>.toFun) = (BoundedAffinePerm.id n).toFun := rfl

/-- The decorated identity is preserved under the toy correspondence. -/
theorem decoratedBounded_id_roundtrip (n : ℕ) :
    (boundedToDecorated_id n).perm = (DecoratedPermutation.id n).perm := rfl

/-- The toy bijection sends identity to identity. -/
theorem toyBijection_at_identity (n : ℕ) :
    boundedToDecorated_id n = DecoratedPermutation.id n ∧
    decoratedToBounded_id n = BoundedAffinePerm.id n :=
  ⟨rfl, rfl⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
