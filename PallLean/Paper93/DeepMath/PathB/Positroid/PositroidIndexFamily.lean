import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# Positroid index families (toy version)

This file provides a kernel-only, finite-dimensional toy model of a
**positroid index family**: a finite collection of subsets of `Fin n`
that contains the empty set and is closed under intersection.

The full positroid story (bounded affine permutations, matroid axioms,
Grassmannian stratification) is far richer; here we only capture the
single structural property of intersection-closure, which is a
necessary feature of positroid cells.

We provide two basic examples:

* `trivialPositroidFamily n` — the family `{∅}`.
* `extremalPositroidFamily n` — the family `{∅, Finset.univ}`.

and verify their cardinalities.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- A **positroid-closed family** at dimension `n`: a finite collection of
    subsets of `Fin n` that contains `∅` and is closed under intersection.
    This captures a structural property of positroid cells
    (intersection-closure). -/
structure PositroidClosedFamily (n : ℕ) where
  family : Finset (Finset (Fin n))
  empty_mem : ∅ ∈ family
  inter_mem : ∀ J K, J ∈ family → K ∈ family → (J ∩ K) ∈ family

/-- The trivial positroid family `{∅}`. -/
def trivialPositroidFamily (n : ℕ) : PositroidClosedFamily n where
  family := {∅}
  empty_mem := Finset.mem_singleton.mpr rfl
  inter_mem := by
    intros J K hJ hK
    rw [Finset.mem_singleton] at hJ hK
    rw [hJ, hK, Finset.empty_inter]
    exact Finset.mem_singleton.mpr rfl

/-- The "extremal" positroid family `{∅, Finset.univ}`. -/
def extremalPositroidFamily (n : ℕ) : PositroidClosedFamily n where
  family := {∅, Finset.univ}
  empty_mem := by simp
  inter_mem := by
    intros J K hJ hK
    rw [Finset.mem_insert, Finset.mem_singleton] at hJ hK
    rcases hJ with hJ | hJ <;> rcases hK with hK | hK
    · subst hJ; rw [Finset.empty_inter]; simp
    · subst hJ; rw [Finset.empty_inter]; simp
    · subst hK; rw [Finset.inter_empty]; simp
    · subst hJ; subst hK; rw [Finset.inter_self]; simp

/-- The cardinality of the trivial family is 1. -/
theorem trivialPositroidFamily_card (n : ℕ) :
    (trivialPositroidFamily n).family.card = 1 := by
  unfold trivialPositroidFamily
  simp

/-- For `n ≥ 1`, the cardinality of the extremal family is 2. -/
theorem extremalPositroidFamily_card (n : ℕ) (hn : 1 ≤ n) :
    (extremalPositroidFamily n).family.card = 2 := by
  unfold extremalPositroidFamily
  rw [Finset.card_insert_of_notMem, Finset.card_singleton]
  intro h
  rw [Finset.mem_singleton] at h
  have hcard : (∅ : Finset (Fin n)).card = (Finset.univ : Finset (Fin n)).card := by rw [h]
  rw [Finset.card_empty, Finset.card_univ, Fintype.card_fin] at hcard
  omega

end PallLean.Paper93.DeepMath.PathB.Positroid
