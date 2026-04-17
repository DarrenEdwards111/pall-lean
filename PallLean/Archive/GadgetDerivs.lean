/-
  GadgetDerivs.lean — Step 1 of Lemma 40(c) discharge: enumerate distinct
  iterDerivList values of a bounded gadget.

  Paper: for bounded g (support t, degree d), the set {iterDerivList A g : A}
  has at most C(t+d, d) distinct values. This is because iterDerivList is
  multilinear and symmetric in its list, so depends only on the multiset of
  indices from g.vars, with total ≤ d. The multi-indices β with β.support ⊆
  g.vars and Σ βᵢ ≤ d are counted by multinomial C(t+d, d) ≤ (t+d+1)^t.

  This file provides:
  - `gadgetDerivIndices g` : Finset of valid multi-indices (β).
  - `gadgetDerivs g` : Finset of derivative polynomials.
  - Cardinality bound: `(gadgetDerivs g).card ≤ N^(t+d)`.
-/
import PallLean.MultilinearSPDP
import PallLean.PAC
import Mathlib.Tactic

namespace GadgetDerivs

open MvPolynomial MultilinearSPDP PAC

/-- Multi-indices `β : Fin N →₀ ℕ` with support in `g.poly.vars` and
total `Σ βᵢ ≤ g.degreeBound`, as a `Finset`.

Implementation: enumerate via functions `g.poly.vars → Fin (d + 1)`, which
is a finite type with `(d+1)^t` elements where `t = g.poly.vars.card`. Then
filter by the sum condition. -/
noncomputable def gadgetDerivIndices {N : ℕ} (g : BoundedGadget N) :
    Finset (Fin N →₀ ℕ) := by
  classical
  exact
    ((Finset.univ : Finset (g.poly.vars → Fin (g.degreeBound + 1))).image
      (fun f =>
        Finsupp.onFinset g.poly.vars
          (fun i : Fin N =>
            if h : i ∈ g.poly.vars then (f ⟨i, h⟩).val else 0)
          (fun i hi => by
            by_contra hne
            simp only [Finsupp.mem_support_iff] at hi
            by_cases hmem : i ∈ g.poly.vars
            · exact hne hmem
            · simp [hmem] at hi))).filter
      (fun β => β.sum (fun _ n => n) ≤ g.degreeBound)

/-- Cardinality bound on `gadgetDerivIndices`: at most
`(g.degreeBound + 1) ^ g.supportSize` elements (from the function-type
enumeration), which is in turn ≤ `N^(g.supportSize + g.degreeBound)` at
scale `N ≥ g.degreeBound + 1`. -/
theorem gadgetDerivIndices_card_le {N : ℕ} (g : BoundedGadget N) :
    (gadgetDerivIndices g).card ≤
      (g.degreeBound + 1) ^ g.poly.vars.card := by
  classical
  unfold gadgetDerivIndices
  calc (gadgetDerivIndices g).card
      ≤ ((Finset.univ : Finset (g.poly.vars → Fin (g.degreeBound + 1))).image _).card := by
        exact Finset.card_filter_le _ _
    _ ≤ (Finset.univ : Finset (g.poly.vars → Fin (g.degreeBound + 1))).card :=
        Finset.card_image_le
    _ = (g.degreeBound + 1) ^ g.poly.vars.card := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_coe]

/-- At scale `N ≥ g.degreeBound + 1`, the enumeration card is ≤ `N^(t+d)`.
Combined with `t ≤ g.supportSize` (which holds by `g.vars_card_le`), we
get the paper's `N^(t+d)` bound. -/
theorem gadgetDerivIndices_card_le_N_pow {N : ℕ} (g : BoundedGadget N)
    (hN : g.degreeBound + 1 ≤ N) :
    (gadgetDerivIndices g).card ≤
      N ^ (g.supportSize + g.degreeBound) := by
  calc (gadgetDerivIndices g).card
      ≤ (g.degreeBound + 1) ^ g.poly.vars.card :=
        gadgetDerivIndices_card_le g
    _ ≤ N ^ g.poly.vars.card :=
        Nat.pow_le_pow_left hN _
    _ ≤ N ^ g.supportSize :=
        Nat.pow_le_pow_right (le_trans (by omega : 1 ≤ g.degreeBound + 1) hN)
          g.vars_card_le
    _ ≤ N ^ (g.supportSize + g.degreeBound) :=
        Nat.pow_le_pow_right (le_trans (by omega : 1 ≤ g.degreeBound + 1) hN)
          (Nat.le_add_right _ _)

/-! ## Step 2a: multi-index → list conversion

For a multi-index `β : Fin N →₀ ℕ`, we need a list `A` such that
`iterDerivList A g = ∂^β g` (the β-multi-derivative). Since `pderiv`
operations commute (standard), any list whose elements (as a multiset)
match `β`'s support counts works.

We pick the canonical list: for each `i ∈ β.support` in sorted order,
append `β i` copies of `i`. -/

/-- Convert a multi-index to a canonical list of its indices (each index
`i` appears `β i` times). Defined via `Finsupp.toMultiset` to inherit
the count and bridge properties directly. -/
noncomputable def multiIndexToList {N : ℕ} (β : Fin N →₀ ℕ) :
    List (Fin N) :=
  (Finsupp.toMultiset β).toList

/-- Bridge: `multiIndexToList β` as a `Multiset` equals `Finsupp.toMultiset β`. -/
theorem multiIndexToList_coe_eq_toMultiset {N : ℕ} (β : Fin N →₀ ℕ) :
    (multiIndexToList β : Multiset (Fin N)) = Finsupp.toMultiset β := by
  unfold multiIndexToList
  exact Multiset.coe_toList _

/-- The length of `multiIndexToList β` equals `β`'s total `Σ βᵢ`. -/
theorem multiIndexToList_length {N : ℕ} (β : Fin N →₀ ℕ) :
    (multiIndexToList β).length = β.sum (fun _ n => n) := by
  unfold multiIndexToList
  rw [Multiset.length_toList]
  rw [Finsupp.card_toMultiset]
  rfl

/-! ## Step 2b: derivative polynomials and Finset

For each multi-index `β`, `gadgetDerivPoly g β` is the polynomial
`iterDerivList (multiIndexToList β) g.poly` — the β-th partial
derivative of `g.poly`. -/

/-- The β-th partial derivative of `g.poly`, via the canonical list. -/
noncomputable def gadgetDerivPoly {N : ℕ} (g : BoundedGadget N)
    (β : Fin N →₀ ℕ) : MvPolynomial (Fin N) ℚ :=
  SPDP.iterDerivList (multiIndexToList β) g.poly

/-- The Finset of gadget derivative polynomials, obtained as the image of
`gadgetDerivIndices` under `gadgetDerivPoly`. -/
noncomputable def gadgetDerivPolyFinset {N : ℕ} (g : BoundedGadget N) :
    Finset (MvPolynomial (Fin N) ℚ) :=
  (gadgetDerivIndices g).image (gadgetDerivPoly g)

/-- The polynomial Finset has cardinality ≤ the index Finset. -/
theorem gadgetDerivPolyFinset_card_le {N : ℕ} (g : BoundedGadget N) :
    (gadgetDerivPolyFinset g).card ≤ (gadgetDerivIndices g).card := by
  exact Finset.card_image_le

/-- At scale `N ≥ degreeBound + 1`, the polynomial Finset has cardinality
≤ `N^(t+d)`. -/
theorem gadgetDerivPolyFinset_card_le_N_pow {N : ℕ} (g : BoundedGadget N)
    (hN : g.degreeBound + 1 ≤ N) :
    (gadgetDerivPolyFinset g).card ≤
      N ^ (g.supportSize + g.degreeBound) :=
  le_trans (gadgetDerivPolyFinset_card_le g)
    (gadgetDerivIndices_card_le_N_pow g hN)

/-! ## Step 2c: permutation invariance of iterDerivList on g-derivatives

For any list `A` with same multiset as `multiIndexToList β`, we have
`iterDerivList A g = iterDerivList (multiIndexToList β) g` by the
commutativity of partial derivatives (via `IterDerivHelpers.iterDerivList_perm`). -/

/-- Convert a list to a count-based multi-index. -/
noncomputable def listToMultiIndex {N : ℕ} (A : List (Fin N)) :
    Fin N →₀ ℕ :=
  Multiset.toFinsupp (A : Multiset (Fin N))

/-- `listToMultiIndex A` at `i` equals `A.count i`. -/
theorem listToMultiIndex_apply {N : ℕ} (A : List (Fin N)) (i : Fin N) :
    (listToMultiIndex A) i = A.count i := by
  unfold listToMultiIndex
  simp [Multiset.toFinsupp_apply, Multiset.coe_count]

-- (multiIndexToList_coe_eq_toMultiset is now immediate from the new definition
-- above via `Multiset.coe_toList`.)

/-- Count property: `(multiIndexToList β).count i = β i`. -/
theorem multiIndexToList_count {N : ℕ} (β : Fin N →₀ ℕ) (i : Fin N) :
    (multiIndexToList β).count i = β i := by
  classical
  rw [← Multiset.coe_count, multiIndexToList_coe_eq_toMultiset,
    Finsupp.count_toMultiset]

/-! ## Step 2d: perm equivalence

For any list `A`, `A` is a permutation of `multiIndexToList (listToMultiIndex A)`.
This lets us convert any `iterDerivList A g` computation into a computation
over a canonical multi-index via `iterDerivList_perm`. -/

/-- `A` and `multiIndexToList (listToMultiIndex A)` have the same count at
every index. -/
theorem listToMultiIndex_count_eq {N : ℕ} (A : List (Fin N)) (i : Fin N) :
    A.count i = (multiIndexToList (listToMultiIndex A)).count i := by
  classical
  rw [multiIndexToList_count, listToMultiIndex_apply]

/-- `A` is a permutation of `multiIndexToList (listToMultiIndex A)`. -/
theorem list_perm_multiIndexToList_listToMultiIndex {N : ℕ} (A : List (Fin N)) :
    A.Perm (multiIndexToList (listToMultiIndex A)) := by
  classical
  rw [List.perm_iff_count]
  intro i
  exact listToMultiIndex_count_eq A i

/-! ## Step 2e: iterDerivList under canonical-list substitution

Via `iterDerivList_perm`, applying iterDerivList to a list `A` gives the same
result as applying it to the canonical `multiIndexToList (listToMultiIndex A)`. -/

/-- `iterDerivList A p = iterDerivList (multiIndexToList (listToMultiIndex A)) p`. -/
theorem iterDerivList_canonical {N : ℕ} (A : List (Fin N))
    (p : MvPolynomial (Fin N) ℚ) :
    SPDP.iterDerivList A p =
    SPDP.iterDerivList (multiIndexToList (listToMultiIndex A)) p :=
  IterDerivHelpers.iterDerivList_perm
    (list_perm_multiIndexToList_listToMultiIndex A) p

/-! ## Step 2f: listToMultiIndex membership in gadgetDerivIndices

If a list `A` has all its elements in `g.poly.vars` and length
`|A| ≤ g.degreeBound`, then `listToMultiIndex A` belongs to
`gadgetDerivIndices g`. -/

/-- For a list `A` with elements in a Finset `s`, every element of
`listToMultiIndex A`'s support is in `s`. -/
theorem listToMultiIndex_support_subset {N : ℕ} (A : List (Fin N))
    (s : Finset (Fin N)) (hA : ∀ i ∈ A, i ∈ s) :
    (listToMultiIndex A).support ⊆ s := by
  classical
  intro i hi
  rw [Finsupp.mem_support_iff, listToMultiIndex_apply] at hi
  have : i ∈ A := List.count_pos_iff.mp (Nat.pos_of_ne_zero hi)
  exact hA i this

/-- The total `Σ (listToMultiIndex A)ᵢ` equals `A.length`. -/
theorem listToMultiIndex_sum {N : ℕ} (A : List (Fin N)) :
    (listToMultiIndex A).sum (fun _ n => n) = A.length := by
  classical
  -- Strategy: use Finsupp.card_toMultiset + inverse equivalence of toFinsupp/toMultiset
  -- Finsupp.card_toMultiset β : Multiset.card (toMultiset β) = β.sum (fun _ => id)
  -- Multiset.toFinsupp_toMultiset m : toMultiset (toFinsupp m) = m
  have h1 : Finsupp.toMultiset (listToMultiIndex A) = (A : Multiset (Fin N)) := by
    unfold listToMultiIndex
    exact Multiset.toFinsupp_toMultiset _
  calc (listToMultiIndex A).sum (fun _ n => n)
      = (listToMultiIndex A).sum (fun _ => id) := rfl
    _ = Multiset.card (Finsupp.toMultiset (listToMultiIndex A)) :=
        (Finsupp.card_toMultiset _).symm
    _ = Multiset.card (A : Multiset (Fin N)) := by rw [h1]
    _ = A.length := by simp [Multiset.coe_card]

/-- **Key:** if `A` has elements in `g.poly.vars` and length ≤ `g.degreeBound`,
then `listToMultiIndex A ∈ gadgetDerivIndices g`. -/
theorem listToMultiIndex_mem_gadgetDerivIndices {N : ℕ} (g : BoundedGadget N)
    (A : List (Fin N))
    (hvar : ∀ i ∈ A, i ∈ g.poly.vars)
    (hlen : A.length ≤ g.degreeBound) :
    listToMultiIndex A ∈ gadgetDerivIndices g := by
  classical
  unfold gadgetDerivIndices
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · -- Membership in the image.
    rw [Finset.mem_image]
    -- Construct f : g.poly.vars → Fin (g.degreeBound + 1)
    refine ⟨fun i : g.poly.vars =>
      ⟨(listToMultiIndex A) i.val, ?_⟩, ?_, ?_⟩
    · -- bound: (listToMultiIndex A) i.val ≤ g.degreeBound < g.degreeBound + 1
      rw [listToMultiIndex_apply]
      have : A.count i.val ≤ A.length := List.count_le_length
      omega
    · exact Finset.mem_univ _
    · -- the constructed onFinset equals listToMultiIndex A
      apply Finsupp.ext
      intro i
      by_cases hi : i ∈ g.poly.vars
      · -- For i ∈ g.poly.vars: onFinset gives (f ⟨i, hi⟩).val = listToMultiIndex A i.
        simp [Finsupp.onFinset_apply, hi]
      · -- For i ∉ g.poly.vars: onFinset gives 0, and listToMultiIndex A i = 0
        -- (since A ⊆ g.poly.vars means A.count i = 0).
        simp only [Finsupp.onFinset_apply, hi, dite_false]
        rw [listToMultiIndex_apply]
        exact (List.count_eq_zero.mpr (fun hA => hi (hvar i hA))).symm
  · -- sum ≤ degreeBound
    rw [listToMultiIndex_sum]
    exact hlen

end GadgetDerivs

