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
`i` appears `β i` times). -/
noncomputable def multiIndexToList {N : ℕ} (β : Fin N →₀ ℕ) :
    List (Fin N) :=
  β.support.toList.flatMap (fun i => List.replicate (β i) i)

/-- The length of `multiIndexToList β` equals `β`'s total `Σ βᵢ`. -/
theorem multiIndexToList_length {N : ℕ} (β : Fin N →₀ ℕ) :
    (multiIndexToList β).length = β.sum (fun _ n => n) := by
  unfold multiIndexToList
  rw [List.length_flatMap]
  simp only [List.length_replicate, Finsupp.sum,
    ← Finset.sum_map_toList]

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

-- Note: multiIndexToList_count (the characterization of counts) is
-- the key technical step to connect gadgetDerivPolyFinset with
-- arbitrary lists via iterDerivList_perm. Proof deferred to future
-- focused session due to repeated Lean elaboration issues with
-- Finset.sum_toList ↔ List.map.sum conversions. The definitions
-- above still support direct construction of β-indexed derivatives.
