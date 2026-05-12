import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset

/-!
# Plücker subset indices for `Gr(k,n)`

The **Plücker indices** for the Grassmannian `Gr(k,n)` are the subsets
`I ⊆ Fin n` with `|I| = k`. Equivalently, they are the elements of
`(Finset.univ : Finset (Fin n)).powersetCard k`. There are `C(n,k)` such
subsets, indexing the homogeneous Plücker coordinates of `Gr(k,n)` in
`ℙ^(C(n,k) - 1)`.

This file defines the collection `pluckerIndices k n` and proves:

* `pluckerIndices_mem`: membership characterisation by cardinality.
* `pluckerIndices_zero`: `pluckerIndices 0 n = {∅}`.
* `pluckerIndices_full`: `pluckerIndices n n = {Finset.univ}`.
* `pluckerIndices_card_too_large`: empty when `n < k`.

This file is **kernel-only**: no `sorry`, no custom `axiom`, only the
kernel axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The set of Plücker indices for `Gr(k,n)`: subsets of `Fin n` of size
    `k`. -/
def pluckerIndices (k n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard k

/-- Membership in `pluckerIndices`: `I ∈ pluckerIndices k n` iff
    `I.card = k`. -/
theorem pluckerIndices_mem {k n : ℕ} (I : Finset (Fin n)) :
    I ∈ pluckerIndices k n ↔ I.card = k := by
  unfold pluckerIndices
  simp [Finset.mem_powersetCard]

/-- `pluckerIndices 0 n` contains only the empty set. -/
theorem pluckerIndices_zero (n : ℕ) :
    pluckerIndices 0 n = {(∅ : Finset (Fin n))} := by
  unfold pluckerIndices
  simp [Finset.powersetCard_zero]

/-- `pluckerIndices n n` contains only the full set. -/
theorem pluckerIndices_full (n : ℕ) :
    pluckerIndices n n = {Finset.univ} := by
  unfold pluckerIndices
  ext J
  rw [Finset.mem_powersetCard, Finset.mem_singleton]
  constructor
  · intro ⟨_, hcard⟩
    -- J.card = n and J ⊆ univ. Since Fintype.card (Fin n) = n, J = univ.
    apply Finset.eq_univ_of_card
    rw [hcard, Fintype.card_fin]
  · intro hJ
    refine ⟨?_, ?_⟩
    · subst hJ; exact Finset.subset_univ _
    · subst hJ
      rw [Finset.card_univ, Fintype.card_fin]

/-- For `k > n`, `pluckerIndices k n` is empty. -/
theorem pluckerIndices_card_too_large (k n : ℕ) (h : n < k) :
    pluckerIndices k n = ∅ := by
  unfold pluckerIndices
  rw [Finset.eq_empty_iff_forall_notMem]
  intro J hJ
  rw [Finset.mem_powersetCard] at hJ
  obtain ⟨hsub, hcard⟩ := hJ
  have hle : J.card ≤ n := by
    calc J.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card hsub
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
  omega

end PallLean.Paper93.DeepMath.PathB.Positroid
