import PallLean.Paper93.Paper283.BridgeAKappaTwoTwoFoldLeibnizExpansion

/-!
# List induction helpers for `pderivListProdSum` and `pderivListProdSumTwice`

This file develops `concat`, `append`, and `flatMap` shape lemmas for
the (recursive) Leibniz sums `pderivListProdSum` and
`pderivListProdSumTwice`.

These helpers are needed to discharge the identity-(3) per-pair sum
because the literal touched-list at an interior block has the shape
`bool ++ adj ++ flatMap states transFactorsForState`, whose `flatMap`
component does **not** reduce by `decide` (it is parametric in
`numStates`).

## Hard rules (CLAUDE.md)
* No `sorry`.  No new axioms.

## Lemmas

* `pderivListProdSum_append`  — split a list at `++`.
* `pderivListProdSumTwice_append` — same for the two-fold variant.
* `pderivListProdSum_flatMap` — Σ over `flatMap`.
* `pderivListProdSumTwice_flatMap` — Σ over `flatMap`, two-fold.

The `_append` lemmas have a clean recursive form (linear in the
left-list); the `_flatMap` lemmas reduce a `flatMap` over a `List` to
an iterated `_append` followed by recursion on the outer list.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open BridgeABlockProductRule
open BridgeAKappaTwoTwoFoldLeibnizExpansion

attribute [local instance] Classical.dec

namespace BridgeAKappaTwoListInductionHelpers

/-! ## Section A: `pderivListProdSum_append` -/

/-- Splitting `pderivListProdSum` at `++`: the partial-derivative sum
of a concatenation is the partial-derivative of the left half times
the right half product, plus the left product times the partial
derivative of the right half. -/
theorem pderivListProdSum_append
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (i : σ) (l₁ l₂ : List (MvPolynomial σ R)) :
    pderivListProdSum i (l₁ ++ l₂) =
      pderivListProdSum i l₁ * l₂.prod +
      l₁.prod * pderivListProdSum i l₂ := by
  induction l₁ with
  | nil =>
      rw [List.nil_append, pderivListProdSum_nil, zero_mul, zero_add,
          List.prod_nil, one_mul]
  | cons x xs ih =>
      rw [List.cons_append, pderivListProdSum_cons, pderivListProdSum_cons]
      rw [ih, List.prod_cons, List.prod_append]
      ring

/-! ## Section B: `pderivListProdSumTwice_append` -/

/-- Splitting `pderivListProdSumTwice` at `++`: the two-fold Leibniz
sum of a concatenation expands by the two-fold product rule on
`(l₁.prod * l₂.prod)`. -/
theorem pderivListProdSumTwice_append
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (v w : σ) (l₁ l₂ : List (MvPolynomial σ R)) :
    pderivListProdSumTwice v w (l₁ ++ l₂) =
      pderivListProdSumTwice v w l₁ * l₂.prod
      + pderivListProdSum v l₁ * pderivListProdSum w l₂
      + pderivListProdSum w l₁ * pderivListProdSum v l₂
      + l₁.prod * pderivListProdSumTwice v w l₂ := by
  unfold pderivListProdSumTwice
  rw [pderivListProdSum_append v]
  rw [map_add]
  rw [pderiv_mul, pderiv_mul]
  rw [pderiv_list_prod, pderiv_list_prod]
  ring

/-! ## Section C: `pderivListProdSum_flatMap` over `List` -/

/-- Helper: the product of a flatMap factors. -/
theorem prod_flatMap
    {σ : Type*} [CommMonoid σ] {α : Type*}
    (l : List α) (f : α → List σ) :
    (l.flatMap f).prod = (l.map (fun a => (f a).prod)).prod := by
  induction l with
  | nil => simp
  | cons a as ih =>
      rw [List.flatMap_cons, List.prod_append]
      rw [List.map_cons, List.prod_cons]
      rw [ih]

/-- `pderivListProdSum` over a `flatMap`: reduces to a recursive
formula reminiscent of the Leibniz rule on the outer list. -/
theorem pderivListProdSum_flatMap
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R] {α : Type*}
    (i : σ) (l : List α) (f : α → List (MvPolynomial σ R)) :
    pderivListProdSum i (l.flatMap f) =
      pderivListProdSum i (l.map (fun a => (f a).prod)) := by
  -- Both sides equal `pderiv i (∏ l.flatMap f) = pderiv i (∏ map ...)`.
  have heq : ((l.flatMap f).prod : MvPolynomial σ R) =
      (l.map (fun a => (f a).prod)).prod := prod_flatMap l f
  have hL := pderiv_list_prod (R := R) i (l.flatMap f)
  have hR := pderiv_list_prod (R := R) i (l.map (fun a => (f a).prod))
  rw [← hL, ← hR, heq]

/-- Combined: `pderivListProdSum_append` instantiated where the
right list is itself a `flatMap`. -/
theorem pderivListProdSum_append_flatMap
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R] {α : Type*}
    (i : σ) (l₁ : List (MvPolynomial σ R))
    (l : List α) (f : α → List (MvPolynomial σ R)) :
    pderivListProdSum i (l₁ ++ l.flatMap f) =
      pderivListProdSum i l₁ * (l.flatMap f).prod +
      l₁.prod * pderivListProdSum i (l.map (fun a => (f a).prod)) := by
  rw [pderivListProdSum_append]
  rw [pderivListProdSum_flatMap]

/-! ## Section D: `pderivListProdSumTwice_flatMap` -/

/-- The two-fold Leibniz sum is invariant under reshaping `flatMap` to
the outer-list product (since both sides equal the same partial
derivative). -/
theorem pderivListProdSumTwice_flatMap
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R] {α : Type*}
    (v w : σ) (l : List α) (f : α → List (MvPolynomial σ R)) :
    pderivListProdSumTwice v w (l.flatMap f) =
      pderivListProdSumTwice v w (l.map (fun a => (f a).prod)) := by
  have heq : ((l.flatMap f).prod : MvPolynomial σ R) =
      (l.map (fun a => (f a).prod)).prod := prod_flatMap l f
  have hL := pderiv_pderiv_list_prod (R := R) v w (l.flatMap f)
  have hR := pderiv_pderiv_list_prod (R := R) v w (l.map (fun a => (f a).prod))
  rw [← hL, ← hR, heq]

/-! ## Section E: cons-pass-through under `pderivListProdSum` for inert -/

/-- If `pderiv i f = 0`, then `pderivListProdSum i (f :: fs) =
f * pderivListProdSum i fs`. -/
theorem pderivListProdSum_cons_inert
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (i : σ) (f : MvPolynomial σ R) (fs : List (MvPolynomial σ R))
    (hf : pderiv i f = 0) :
    pderivListProdSum i (f :: fs) = f * pderivListProdSum i fs := by
  rw [pderivListProdSum_cons]
  rw [hf, zero_mul, zero_add]

/-! ## Axiom audit anchors -/

#print axioms pderivListProdSum_append
#print axioms pderivListProdSumTwice_append
#print axioms prod_flatMap
#print axioms pderivListProdSum_flatMap
#print axioms pderivListProdSum_append_flatMap
#print axioms pderivListProdSumTwice_flatMap
#print axioms pderivListProdSum_cons_inert

end BridgeAKappaTwoListInductionHelpers

end PallLean.Paper93.Paper283

namespace PallLean.Paper93.Paper283

namespace BridgeAKappaTwoListInductionHelpers

open MvPolynomial
open BridgeABlockProductRule
open BridgeAKappaTwoTwoFoldLeibnizExpansion

attribute [local instance] Classical.dec

/-! ## Section F: inert-list pass-through

If every factor in `l₁` is inert under both `pderiv v` and `pderiv w`,
then `pderivListProdSumTwice v w (l₁ ++ l₂) = l₁.prod *
pderivListProdSumTwice v w l₂`.  This is the structural backbone of
the Section J cross-term-vanishing argument: pulling all inert factors
through the two-fold Leibniz expansion. -/

/-- If every factor in `l` is inert under `pderiv v`
(`pderiv v f = 0` for all `f ∈ l`), then
`pderivListProdSum v l = 0`. -/
theorem pderivListProdSum_eq_zero_of_all_inert
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (v : σ) (l : List (MvPolynomial σ R))
    (hl : ∀ f ∈ l, pderiv v f = 0) :
    pderivListProdSum v l = 0 := by
  induction l with
  | nil => exact pderivListProdSum_nil v
  | cons x xs ih =>
      rw [pderivListProdSum_cons]
      have hx : pderiv v x = 0 := hl x (List.mem_cons_self)
      have ihxs : pderivListProdSum v xs = 0 := by
        apply ih
        intro f hf
        exact hl f (List.mem_cons_of_mem x hf)
      rw [hx, zero_mul, zero_add, ihxs, mul_zero]

/-- If every factor in `l` is inert under both `pderiv v` and
`pderiv w`, then `pderivListProdSumTwice v w l = 0`. -/
theorem pderivListProdSumTwice_eq_zero_of_all_inert
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (v w : σ) (l : List (MvPolynomial σ R))
    (hv : ∀ f ∈ l, pderiv v f = 0)
    (_hw : ∀ f ∈ l, pderiv w f = 0) :
    pderivListProdSumTwice v w l = 0 := by
  unfold pderivListProdSumTwice
  rw [pderivListProdSum_eq_zero_of_all_inert v l hv]
  exact map_zero _

/-- **Inert prefix pass-through**: if every factor in the prefix `l₁`
is inert under both `pderiv v` and `pderiv w`, then the two-fold
Leibniz sum of `l₁ ++ l₂` collapses to
`l₁.prod * pderivListProdSumTwice v w l₂`. -/
theorem pderivListProdSumTwice_append_inert_prefix
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (v w : σ) (l₁ l₂ : List (MvPolynomial σ R))
    (hv : ∀ f ∈ l₁, pderiv v f = 0)
    (hw : ∀ f ∈ l₁, pderiv w f = 0) :
    pderivListProdSumTwice v w (l₁ ++ l₂) =
      l₁.prod * pderivListProdSumTwice v w l₂ := by
  rw [pderivListProdSumTwice_append]
  rw [pderivListProdSumTwice_eq_zero_of_all_inert v w l₁ hv hw]
  rw [pderivListProdSum_eq_zero_of_all_inert v l₁ hv]
  rw [pderivListProdSum_eq_zero_of_all_inert w l₁ hw]
  ring

/-- **Inert suffix pass-through**: dual of `_inert_prefix`. -/
theorem pderivListProdSumTwice_append_inert_suffix
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (v w : σ) (l₁ l₂ : List (MvPolynomial σ R))
    (hv : ∀ f ∈ l₂, pderiv v f = 0)
    (hw : ∀ f ∈ l₂, pderiv w f = 0) :
    pderivListProdSumTwice v w (l₁ ++ l₂) =
      pderivListProdSumTwice v w l₁ * l₂.prod := by
  rw [pderivListProdSumTwice_append]
  rw [pderivListProdSumTwice_eq_zero_of_all_inert v w l₂ hv hw]
  rw [pderivListProdSum_eq_zero_of_all_inert v l₂ hv]
  rw [pderivListProdSum_eq_zero_of_all_inert w l₂ hw]
  ring

#print axioms pderivListProdSum_eq_zero_of_all_inert
#print axioms pderivListProdSumTwice_eq_zero_of_all_inert
#print axioms pderivListProdSumTwice_append_inert_prefix
#print axioms pderivListProdSumTwice_append_inert_suffix

end BridgeAKappaTwoListInductionHelpers

end PallLean.Paper93.Paper283
