import PallLean.Paper93.DeepMath.PathB.Positroid.PositroidIndexFamily
import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermutation
import PallLean.Paper93.DeepMath.PathB.Positroid.BoundedAffinePerm

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The trivial positroid cell at dimension n: the cell indexed by the identity decorated permutation. -/
structure TrivialPositroidCell (n : ℕ) where
  decoratedPerm : DecoratedPermutation n
  /-- The cell is at the identity. -/
  is_identity : decoratedPerm = DecoratedPermutation.id n

/-- The unique trivial positroid cell. -/
def trivialPositroidCell (n : ℕ) : TrivialPositroidCell n where
  decoratedPerm := DecoratedPermutation.id n
  is_identity := rfl

/-- The trivial positroid cell has identity decorated permutation. -/
theorem trivialPositroidCell_decoratedPerm (n : ℕ) :
    (trivialPositroidCell n).decoratedPerm = DecoratedPermutation.id n := rfl

/-- The trivial positroid cell at n=2 corresponds to the identity. -/
theorem trivialPositroidCell_n2 :
    (trivialPositroidCell 2).decoratedPerm = DecoratedPermutation.id 2 := rfl

end PallLean.Paper93.DeepMath.PathB.Positroid
