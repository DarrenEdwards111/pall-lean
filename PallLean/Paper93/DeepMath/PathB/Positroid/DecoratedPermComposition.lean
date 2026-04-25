import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermutation

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- Composition of two decorated permutations: compose underlying perms, keep decoration of first. -/
def DecoratedPermutation.compose {n : ℕ} (σ τ : DecoratedPermutation n) :
    DecoratedPermutation n where
  perm := σ.perm.trans τ.perm
  decoration := σ.decoration

/-- Composition with identity on the right preserves the perm. -/
theorem DecoratedPermutation.compose_id_right {n : ℕ} (σ : DecoratedPermutation n) :
    (σ.compose (DecoratedPermutation.id n)).perm = σ.perm := by
  unfold DecoratedPermutation.compose DecoratedPermutation.id
  exact Equiv.trans_refl _

/-- Composition with identity on the left preserves the perm (with id's decoration). -/
theorem DecoratedPermutation.id_compose {n : ℕ} (σ : DecoratedPermutation n) :
    ((DecoratedPermutation.id n).compose σ).perm = σ.perm := by
  unfold DecoratedPermutation.compose DecoratedPermutation.id
  exact Equiv.refl_trans _

/-- Identity composed with itself is identity. -/
theorem DecoratedPermutation.id_compose_id (n : ℕ) :
    ((DecoratedPermutation.id n).compose (DecoratedPermutation.id n)).perm =
    (DecoratedPermutation.id n).perm :=
  DecoratedPermutation.compose_id_right _

end PallLean.Paper93.DeepMath.PathB.Positroid
