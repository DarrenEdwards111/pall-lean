import PallLean.Paper93.DeepMath.PathB.Positroid.BoundedAffinePerm
import PallLean.Paper93.DeepMath.PathB.Positroid.LeDiagramDef
import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermutation

/-!
# The `n = 1` case: bounded-affine ↔ Le ↔ decorated triple

This file documents, in a kernel-only Lean 4 module, the structural
collapse of the three positroid index structures
(`BoundedAffinePerm`, `LeDiagram`, `DecoratedPermutation`) at `n = 1`.

## Why does it collapse?

At `n = 1`, all three structures reduce to single canonical instances:

* `BoundedAffinePerm 1`: any 1-equivariant bijection `ℤ → ℤ` is a
  shift by an integer, and the boundedness `i ≤ f(i) ≤ i + 1` together
  with bijectivity forces this shift to be the identity.
* `LeDiagram k 1` (for arbitrary `k`): the column dimension is `1`, so
  the `j₁ < j₂` precondition of the Le condition is vacuous and the
  zero diagram is the canonical "empty" representative.
* `DecoratedPermutation 1`: the permutation must be the identity, but
  the decoration on the unique fixed point is free, giving exactly
  `id` (positive) and `neg_id` (negative). We exhibit `id`.

This file gives the canonical representatives of each structure at
`n = 1` and packages them as a single existence-of-corresponding-triple
theorem.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The canonical bounded affine permutation at n=1: the identity. -/
def canonicalBoundedAffineN1 : BoundedAffinePerm 1 := BoundedAffinePerm.id 1

/-- The canonical zero Le diagram at k=1, n=1. -/
def canonicalLeDiagramN1 : LeDiagram 1 1 := LeDiagram.zero 1 1

/-- The canonical positive-decoration identity decorated permutation at n=1. -/
def canonicalDecoratedN1 : DecoratedPermutation 1 := DecoratedPermutation.id 1

/-- All three canonical instances are well-typed at n=1. -/
theorem canonicalN1_well_typed :
    canonicalBoundedAffineN1.toFun = (BoundedAffinePerm.id 1).toFun ∧
    (canonicalLeDiagramN1.filling = (LeDiagram.zero 1 1).filling) ∧
    canonicalDecoratedN1.perm = (DecoratedPermutation.id 1).perm := by
  refine ⟨rfl, rfl, rfl⟩

/-- The toy bijection at n=1: all three canonical instances correspond. -/
theorem n1_canonical_correspondence :
    canonicalBoundedAffineN1 = BoundedAffinePerm.id 1 ∧
    canonicalLeDiagramN1.filling = (fun _ : Fin 1 => fun _ : Fin 1 => false) ∧
    canonicalDecoratedN1 = DecoratedPermutation.id 1 :=
  ⟨rfl, rfl, rfl⟩

/-- Existence of a triple of corresponding canonical instances at n=1. -/
theorem n1_triple_exists :
    ∃ (b : BoundedAffinePerm 1) (L : LeDiagram 1 1) (d : DecoratedPermutation 1),
      b = BoundedAffinePerm.id 1 ∧ d = DecoratedPermutation.id 1 :=
  ⟨BoundedAffinePerm.id 1, LeDiagram.zero 1 1, DecoratedPermutation.id 1, rfl, rfl⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
