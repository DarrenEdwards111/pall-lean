import PallLean.Paper93.DeepMath.PathB.Positroid.LeDiagramDef
import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermutation

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The toy map from a Le diagram to a decorated permutation: returns the identity decorated permutation. -/
def LeDiagram.toDecoratedToy (n : ℕ) (_D : LeDiagram n n) : DecoratedPermutation n :=
  DecoratedPermutation.id n

/-- The zero Le diagram maps to the identity decorated permutation. -/
theorem LeDiagram.zero_to_decorated (n : ℕ) :
    (LeDiagram.zero n n).toDecoratedToy n = DecoratedPermutation.id n := rfl

/-- The one Le diagram maps to the identity decorated permutation. -/
theorem LeDiagram.one_to_decorated (n : ℕ) :
    (LeDiagram.one n n).toDecoratedToy n = DecoratedPermutation.id n := rfl

/-- The toy map sends every Le diagram to the identity decorated permutation (constant function). -/
theorem LeDiagram.toDecoratedToy_const (n : ℕ) (D : LeDiagram n n) :
    D.toDecoratedToy n = DecoratedPermutation.id n := rfl

end PallLean.Paper93.DeepMath.PathB.Positroid
