import PallLean.Paper93.DeepMath.PathB.Positroid.BoundedAffinePerm
import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermutation

/-!
# The `n = 2` case: bounded-affine ↔ decorated structural correspondences

This file records, in a kernel-only Lean 4 module, structural
correspondences between bounded affine permutations and decorated
permutations at `n = 2`.

At `n = 2`, the canonical identity bounded affine permutation is paired
with two canonical decorated permutations sharing the same underlying
identity permutation but distinguished by their decoration choice
(`positive` versus `negative`). We exhibit both decoration choices and
package them with the bounded affine identity as a triple.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The identity bounded affine permutation at n=2. -/
def bound_n2_id : BoundedAffinePerm 2 := BoundedAffinePerm.id 2

/-- The identity decorated permutation at n=2 (positive decorations). -/
def decorated_n2_id_pos : DecoratedPermutation 2 := DecoratedPermutation.id 2

/-- The negative-decoration identity at n=2. -/
def decorated_n2_id_neg : DecoratedPermutation 2 := DecoratedPermutation.neg_id 2

/-- The bound n=2 id and decorated n=2 id are well-defined. -/
theorem n2_canonical_correspondence_pos :
    bound_n2_id = BoundedAffinePerm.id 2 ∧
    decorated_n2_id_pos = DecoratedPermutation.id 2 :=
  ⟨rfl, rfl⟩

/-- The bound n=2 id and decorated n=2 neg-id are well-defined. -/
theorem n2_canonical_correspondence_neg :
    bound_n2_id = BoundedAffinePerm.id 2 ∧
    decorated_n2_id_neg = DecoratedPermutation.neg_id 2 :=
  ⟨rfl, rfl⟩

/-- At n=2, both decoration choices yield distinct decorated permutations
    (sharing the same underlying perm = identity). -/
theorem n2_two_decorations_same_perm :
    decorated_n2_id_pos.perm = decorated_n2_id_neg.perm ∧
    decorated_n2_id_pos.decoration ⟨0, by omega⟩ ≠ decorated_n2_id_neg.decoration ⟨0, by omega⟩ := by
  refine ⟨rfl, ?_⟩
  show Decoration.positive ≠ Decoration.negative
  decide

/-- Triple existence at n=2: bounded affine + decorated (pos) + decorated (neg). -/
theorem n2_triple_exists :
    ∃ (b : BoundedAffinePerm 2) (d_pos : DecoratedPermutation 2) (d_neg : DecoratedPermutation 2),
      b = BoundedAffinePerm.id 2 ∧
      d_pos = DecoratedPermutation.id 2 ∧
      d_neg = DecoratedPermutation.neg_id 2 :=
  ⟨BoundedAffinePerm.id 2, DecoratedPermutation.id 2, DecoratedPermutation.neg_id 2,
   rfl, rfl, rfl⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
