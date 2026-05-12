import PallLean.Paper93.DeepMath.PathB.Positroid.LeDiagramDef
import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermutation

/-!
# Concrete n=2 Le-diagram and decorated-permutation examples

This file provides concrete `n=2` instances and basic structural theorems for
both `LeDiagram` (on the 2×2 grid) and `DecoratedPermutation` (at `n=2`).
These instances are the smallest non-trivial cases beyond the n=1 collapse,
and they appear repeatedly throughout the positroid Path B development.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The 2×2 zero Le diagram. -/
def le_diagram_2x2_zero : LeDiagram 2 2 := LeDiagram.zero 2 2

/-- The 2×2 all-ones Le diagram. -/
def le_diagram_2x2_one : LeDiagram 2 2 := LeDiagram.one 2 2

/-- The identity decorated permutation at n=2. -/
def decorated_n2_id : DecoratedPermutation 2 := DecoratedPermutation.id 2

/-- The negative-decoration identity at n=2. -/
def decorated_n2_neg_id : DecoratedPermutation 2 := DecoratedPermutation.neg_id 2

/-- The 2×2 zero Le diagram has all-false filling. -/
theorem le_diagram_2x2_zero_filling (i : Fin 2) (j : Fin 2) :
    le_diagram_2x2_zero.filling i j = false := rfl

/-- The 2×2 all-ones Le diagram has all-true filling. -/
theorem le_diagram_2x2_one_filling (i : Fin 2) (j : Fin 2) :
    le_diagram_2x2_one.filling i j = true := rfl

/-- The decorated identity at n=2 has identity permutation. -/
theorem decorated_n2_id_perm :
    decorated_n2_id.perm = Equiv.refl (Fin 2) := rfl

/-- The decorated identity at n=2 has all-positive decoration. -/
theorem decorated_n2_id_decoration (i : Fin 2) :
    decorated_n2_id.decoration i = Decoration.positive := rfl

/-- The two canonical decorated permutations at n=2 differ in their decoration. -/
theorem decorated_n2_id_vs_neg_id_decoration_differ :
    decorated_n2_id.decoration ⟨0, by omega⟩ ≠
    decorated_n2_neg_id.decoration ⟨0, by omega⟩ := by
  show Decoration.positive ≠ Decoration.negative
  decide

end PallLean.Paper93.DeepMath.PathB.Positroid
