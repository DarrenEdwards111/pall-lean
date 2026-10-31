import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRouteFProbe
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Route F gap test — the product-sheet locality failure (confirmed)

The honest test of input (1) of `ComputationalDepthProfileCount`: does the per-sheet locality (each sheet
has bounded rank / `O(log n)`-determined profiles) survive the **product-sheet** structure of the
Cook–Levin compilation?  The answer, computed and proved here, is **no** — and this is exactly the
documented P-side gap.

## Computational finding (`native_decide`)

`kron` is the Kronecker (tensor) product over `F₂` — combining two sheets couples their rows/cols
multiplicatively, the "product sheet" structure.  For a single rank-`2` sheet:

* `f2rank sheet = 2`;
* `f2rank (kron sheet sheet) = 4`;
* `f2rank (kron sheet (kron sheet sheet)) = 8`.

The rank **multiplies** under product: `m` sheets ⇒ rank `2^m`.  (Confirmed for two different rank-`2`
sheets, so it is not an identity artifact.)

## The proved principle

`product_count_ge_two_pow`: a product of `m` factors each with profile count `≥ 2` has total count `≥ 2^m`.
Combined with exp-beats-poly (`Nat.exists_poly_lt_pow`): `2^m` exceeds **every** polynomial once `m` is
super-logarithmic.

## Conclusion — the gap is real

The Cook–Levin compilation is a product of `m = poly(n)` local sheets (≈ one per tableau cell).  If these
sheets were *independent* (naive product), the profile count / SPDP rank would be `≥ 2^{poly(n)}` —
**exponential**, blowing through the required `n²⁰⁰`.  So:

* per-sheet locality is **true** (each sheet is `O(log n)`-determined, low rank), but
* it does **not** transfer to the product — `ComputationalDepthProfileCount.profileSpace_card_le_poly`
  applies to *one* `O(log n)`-window, not to a product of poly-many of them.

Therefore `CookLevinFrontierHyp` cannot be discharged by naive per-sheet locality: it **requires the sheets
to be coupled / restructured** (lane classification, shared-profile collapse) so the product does *not*
multiply rank.  That structural lemma is the genuine open content — this test pins it down rather than
papering over it.  Nothing here asserts `CookLevinFrontierHyp`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ProductSheetGap

open RouteFProbe (f2rank)

/-- Kronecker (tensor) product of two `F₂` matrices — the product-sheet structure. -/
def kron (A B : List (List Bool)) : List (List Bool) :=
  A.flatMap (fun arow => B.map (fun brow => arow.flatMap (fun a => brow.map (fun b => a && b))))

/-- A single rank-`2` sheet. -/
def sheet : List (List Bool) := [[true, false], [false, true]]
/-- A second, nontrivial rank-`2` sheet (not the identity). -/
def sheet2 : List (List Bool) := [[true, true], [false, true]]

/-! ### Rank multiplies under product (`native_decide`) -/

theorem sheet_rank : f2rank sheet = 2 := by native_decide
theorem two_sheets_rank : f2rank (kron sheet sheet) = 4 := by native_decide
theorem three_sheets_rank : f2rank (kron sheet (kron sheet sheet)) = 8 := by native_decide
theorem sheet2_rank : f2rank sheet2 = 2 := by native_decide
theorem two_sheets2_rank : f2rank (kron sheet2 sheet2) = 4 := by native_decide
theorem three_sheets2_rank : f2rank (kron sheet2 (kron sheet2 sheet2)) = 8 := by native_decide

/-! ### The proved principle: independent product sheets ⇒ exponential count -/

/-- A product of `m` factors each with count `≥ 2` has total count `≥ 2^m` (exponential in the number of
sheets). -/
theorem product_count_ge_two_pow {m : ℕ} (count : Fin m → ℕ) (h2 : ∀ i, 2 ≤ count i) :
    2 ^ m ≤ ∏ i, count i := by
  calc 2 ^ m = ∏ _i : Fin m, 2 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ i, count i := Finset.prod_le_prod (fun _ _ => by norm_num) (fun i _ => h2 i)

end PallLean.Paper93.DeepMath.PathB.ProductSheetGap

#print axioms PallLean.Paper93.DeepMath.PathB.ProductSheetGap.product_count_ge_two_pow
