import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# Structural facts about `satFamily n` at large `n`

This kernel-only file records a handful of structural facts about the
SAT decider's principal-minor family `satFamily n` at the concrete large
parameter values `n = 50` and `n = 100`. Each fact follows directly from
the lemmas in `SatFamilyDefinition.lean` (`satFamily_card`,
`satFamily_mem_empty`, `satFamily_mem_univ`, `satFamily_subset_iff`).

These are intentionally simple: they exercise the definition
`satFamily n = {∅, Finset.univ}` at large `n` and verify that the
cardinality lemma evaluates correctly, that both extremal witnesses are
present, and that a concrete proper non-empty subset (a singleton) is
*not* in the family.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB

/-! ## Facts at `n = 50` -/

/-- `satFamily 50` has exactly two elements. -/
theorem satFamily_n50_card : (satFamily 50).card = 2 :=
  satFamily_card 50 (by decide)

/-- The empty subset of `Fin 50` is in `satFamily 50`. -/
theorem satFamily_n50_mem_empty : (∅ : Finset (Fin 50)) ∈ satFamily 50 :=
  satFamily_mem_empty 50

/-- The full subset of `Fin 50` is in `satFamily 50`. -/
theorem satFamily_n50_mem_univ :
    (Finset.univ : Finset (Fin 50)) ∈ satFamily 50 :=
  satFamily_mem_univ 50

/-! ## Facts at `n = 100` -/

/-- `satFamily 100` has exactly two elements. -/
theorem satFamily_n100_card : (satFamily 100).card = 2 :=
  satFamily_card 100 (by decide)

/-- The empty subset of `Fin 100` is in `satFamily 100`. -/
theorem satFamily_n100_mem_empty : (∅ : Finset (Fin 100)) ∈ satFamily 100 :=
  satFamily_mem_empty 100

/-- The full subset of `Fin 100` is in `satFamily 100`. -/
theorem satFamily_n100_mem_univ :
    (Finset.univ : Finset (Fin 100)) ∈ satFamily 100 :=
  satFamily_mem_univ 100

/-! ## A specific singleton is not in `satFamily 50`

The singleton `{⟨0, _⟩}` of `Fin 50` is a proper non-empty subset and
hence neither equals `∅` nor `Finset.univ`. By the membership
characterisation `satFamily_subset_iff`, it cannot lie in
`satFamily 50`. -/

/-- The singleton `{0}` is not in `satFamily 50`. -/
theorem satFamily_n50_singleton_zero_not_mem :
    ({(⟨0, by decide⟩ : Fin 50)} : Finset (Fin 50)) ∉ satFamily 50 := by
  -- Reduce membership to the disjunction characterisation.
  rw [satFamily_subset_iff]
  -- Now we must rule out both cases.
  rintro (h | h)
  · -- `{0} = ∅` would force the cardinalities to match.
    have hcard : ({(⟨0, by decide⟩ : Fin 50)} : Finset (Fin 50)).card
                  = (∅ : Finset (Fin 50)).card := by rw [h]
    rw [Finset.card_singleton, Finset.card_empty] at hcard
    -- `1 = 0`
    exact (Nat.one_ne_zero hcard).elim
  · -- `{0} = Finset.univ` would force `Finset.univ` to have cardinality 1.
    have hcard : ({(⟨0, by decide⟩ : Fin 50)} : Finset (Fin 50)).card
                  = (Finset.univ : Finset (Fin 50)).card := by rw [h]
    rw [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at hcard
    -- `1 = 50`
    exact absurd hcard (by decide)

end PallLean.Paper93.DeepMath.PathB.Positroid
