import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermutation
import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermComposition
import Mathlib.Logic.Equiv.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- Identity composed with identity gives identity (on perm component). -/
theorem id_compose_id_perm (n : ℕ) :
    ((DecoratedPermutation.id n).compose (DecoratedPermutation.id n)).perm =
    (DecoratedPermutation.id n).perm :=
  DecoratedPermutation.id_compose_id n

/-- Composing with id on right preserves perm. -/
theorem compose_id_right_perm {n : ℕ} (σ : DecoratedPermutation n) :
    (σ.compose (DecoratedPermutation.id n)).perm = σ.perm :=
  DecoratedPermutation.compose_id_right σ

/-- Composing with id on left preserves perm (with id's decoration). -/
theorem id_compose_perm {n : ℕ} (σ : DecoratedPermutation n) :
    ((DecoratedPermutation.id n).compose σ).perm = σ.perm :=
  DecoratedPermutation.id_compose σ

end PallLean.Paper93.DeepMath.PathB.Positroid
