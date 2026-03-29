import PallLean.WithinProfile

/-! # Layer 4: Assembly — structural results toward width_to_rank

Layers 1-3 reduce the Width⇒Rank problem to counting:

* Layer 1 (Leibniz): iterDerivList S (∏ f_i) ∈ span of allocation products
* Layer 2 (Profile): allocations group into ≤ (w+1)^m profiles
* Layer 3 (Within-profile): per-factor derivatives are Nodup ⊆ vars, derivs commute

This file proves the remaining structural facts:
* `alloc_product_vars_subset` — allocation product vars ⊆ ⋃ factor vars
* `factor_vars_union_card_le` — |⋃ factor vars| ≤ m × width

The final bound (m·w)^(3w) requires the paper's §9 type-based profile
decomposition, which groups the m factors into |T| = O(1) types and
uses symmetric tensor powers. This is the content of the monolithic
`width_to_rank` axiom in MultilinearSPDP.lean.

## Why the axiom can't be eliminated by width specialization

For width=4, the naive approach gives 2^(4m) multilinear monomials,
which exceeds (4m)^12 for large m. The paper avoids this by grouping
factors into O(1) types (compiler property), making the profile count
independent of m. Formalizing this requires the full §9.2-9.3
type classification and block-factorable diagonal-basis structure.
-/

namespace SPDP

open MvPolynomial Finset

variable {n : ℕ} {F : Type*} [CommRing F]

/-- Vars of an allocation product ⊆ ⋃_i vars(factor i). -/
theorem alloc_product_vars_subset {κ m : ℕ}
    (S : List (Fin n)) (hS : S.length = κ)
    (α : DerivAlloc κ m)
    (factor : Fin m → MvPolynomial (Fin n) F) :
    (∏ i : Fin m, iterDerivList (allocatedDerivs S hS α i) (factor i)).vars ⊆
    Finset.univ.biUnion (fun i => (factor i).vars) := by
  intro v hv
  have h1 := MvPolynomial.vars_prod
    (fun i : Fin m => iterDerivList (allocatedDerivs S hS α i) (factor i)) hv
  rw [Finset.mem_biUnion] at h1 ⊢
  obtain ⟨i, hi, hv_i⟩ := h1
  exact ⟨i, hi, vars_iterDerivList_subset _ _ hv_i⟩

/-- The union of all factor vars has card ≤ m * width. -/
theorem factor_vars_union_card_le (m : ℕ)
    (factor : Fin m → MvPolynomial (Fin n) F)
    (width : ℕ) (hfactor_width : ∀ i, (factor i).vars.card ≤ width) :
    (Finset.univ.biUnion (fun i : Fin m => (factor i).vars)).card ≤ m * width := by
  calc (Finset.univ.biUnion (fun i : Fin m => (factor i).vars)).card
      ≤ ∑ i : Fin m, (factor i).vars.card := Finset.card_biUnion_le
    _ ≤ ∑ _ : Fin m, width := Finset.sum_le_sum (fun i _ => hfactor_width i)
    _ = m * width := by simp [Finset.sum_const, Finset.card_fin]

end SPDP
