import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import Mathlib.Data.Finset.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB

/-- Extended SAT family at n ≥ 1 includes ∅, all singletons, and univ. -/
def satFamilyExtended (n : ℕ) : Finset (Finset (Fin n)) :=
  (satFamily n) ∪ (Finset.univ.image (fun i : Fin n => ({i} : Finset (Fin n))))

theorem satFamilyExtended_contains_empty (n : ℕ) :
    ∅ ∈ satFamilyExtended n := by
  unfold satFamilyExtended
  exact Finset.mem_union.mpr (Or.inl (satFamily_mem_empty n))

theorem satFamilyExtended_contains_univ (n : ℕ) :
    (Finset.univ : Finset (Fin n)) ∈ satFamilyExtended n := by
  unfold satFamilyExtended
  exact Finset.mem_union.mpr (Or.inl (satFamily_mem_univ n))

theorem satFamilyExtended_supset_satFamily (n : ℕ) :
    satFamily n ⊆ satFamilyExtended n := by
  unfold satFamilyExtended
  exact Finset.subset_union_left

end PallLean.Paper93.DeepMath.PathB.Positroid
