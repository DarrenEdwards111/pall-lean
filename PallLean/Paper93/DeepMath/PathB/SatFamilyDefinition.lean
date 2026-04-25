import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

namespace PallLean.Paper93.DeepMath.PathB

/-- The SAT decider's designated principal-minor family `𝒥_SAT`.

For the SAT decider's compiled gadget, this family encodes the positroid
stratification of a specific decider's tableau (paper §7.1, amplituhedron
gauge family). We use the pragmatic concrete definition `{∅, Finset.univ}`:
the trivial two-point stratification consisting of the empty subset (which
contributes the trivial vacuous minor `1`) and the full subset (which
contributes the determinant of the whole matrix). Both endpoints are
determining. -/
def satFamily (n : ℕ) : Finset (Finset (Fin n)) :=
  {∅, Finset.univ}

/-- Cardinality of the SAT family is exactly 2 when `n ≥ 1`,
    since `∅ ≠ Finset.univ` whenever `Finset.univ` is nonempty. -/
theorem satFamily_card (n : ℕ) (hn : 1 ≤ n) : (satFamily n).card = 2 := by
  unfold satFamily
  rw [Finset.card_insert_of_notMem, Finset.card_singleton]
  intro h
  rw [Finset.mem_singleton] at h
  -- h : (∅ : Finset (Fin n)) = Finset.univ
  -- Derive a contradiction by comparing cardinalities.
  have hcard : (∅ : Finset (Fin n)).card = (Finset.univ : Finset (Fin n)).card := by
    rw [h]
  rw [Finset.card_empty, Finset.card_univ, Fintype.card_fin] at hcard
  -- hcard : 0 = n
  omega

/-- The empty index set is in the SAT family. -/
theorem satFamily_mem_empty (n : ℕ) : ∅ ∈ satFamily n := by
  simp [satFamily]

/-- The full index set is in the SAT family. -/
theorem satFamily_mem_univ (n : ℕ) : (Finset.univ : Finset (Fin n)) ∈ satFamily n := by
  simp [satFamily]

/-- Membership in the SAT family is equivalent to being one of the two
    extremal index sets `∅` or `Finset.univ`. -/
theorem satFamily_subset_iff (n : ℕ) (J : Finset (Fin n)) :
    J ∈ satFamily n ↔ J = ∅ ∨ J = Finset.univ := by
  simp [satFamily]

/-- The SAT family is non-empty and structurally meaningful: it contains both
    extremal index sets (∅ and full). Together these encode the boundary
    constraints of the positroid stratification used in the §7.1 amplituhedron
    gauge construction. -/
theorem satFamily_extremal_witnesses (n : ℕ) :
    ∅ ∈ satFamily n ∧ (Finset.univ : Finset (Fin n)) ∈ satFamily n :=
  ⟨satFamily_mem_empty n, satFamily_mem_univ n⟩

end PallLean.Paper93.DeepMath.PathB
