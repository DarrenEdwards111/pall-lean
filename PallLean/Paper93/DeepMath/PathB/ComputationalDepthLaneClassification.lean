import PallLean.Paper93.DeepMath.PathB.ComputationalDepthProductSheetGap
import Mathlib.Data.Fintype.BigOperators

/-!
# Route F — the lane-classification claim, stated and its mechanism proved

The previous file (`ComputationalDepthProductSheetGap`) confirmed the gap: an *independent* (tensor)
product of `m` sheets multiplies rank to `2^m`.  This file states the structural fix the paper needs —
**lane classification** — proves the mechanism, and tests a *coupled* product.

## The claim, precisely

The `m` Cook–Levin sheets do not live on disjoint variables; they share the tableau.  **Lane
classification** is the claim that all `m` sheets *factor through the same `d` "lanes"*: each sheet's rows
depend only on a shared `d`-class partition (`LaneFactored`), with `d = poly(n)`.

## The mechanism, proved

* `profileCount_le_of_laneFactored` — a lane-factored sheet has `≤ d` distinct profiles.
* `laneFactored_prod` — **the key**: the (Hadamard / pointwise) product of *any number* `m` of sheets that
  share the same `d` lanes is itself lane-factored through those `d` lanes.
* `product_profileCount_le` — hence the product of `m` shared-lane sheets has `≤ d` distinct profiles
  **regardless of `m`** — no `2^m` blow-up.  With `d = poly(n)` (a profile = an `O(log n)` window;
  `ProfileCount.profileSpace_card_le_poly`) this is `poly(n)` rank.

## Coupled vs independent — computed (`native_decide`)

* `coupled_stays_bounded` / `coupled_three_bounded` — a Hadamard product of shared-lane sheets keeps
  `f2rank ≤ 2` (= #lanes), for `2` and `3+` factors.
* `independent_explodes` — the tensor product of the *same* sheets jumps to `4` (`= 2²`).

## Honest status

**Proved:** *if* the sheets are lane-classified (share `d = poly(n)` lanes), the product rank stays
`poly(n)`.  The coupling really does prevent the multiplication — the mechanism is sound.

**Open (the genuine remaining content of `CookLevinFrontierHyp`):** that the *actual* Cook–Levin
compilation's `m = poly(n)` sheets **are** lane-classified through `poly(n)` shared lanes.  This is now a
single precise, falsifiable structural claim (`CookLevinLaneClassified` below) — the make-or-break lemma.
It is **not** asserted here; proving it is the open P-side frontier.
-/

namespace PallLean.Paper93.DeepMath.PathB.LaneClassification

open Finset
open RouteFProbe (f2rank)
open ProductSheetGap (kron)

/-- A sheet's rows are **lane-factored** through `d` lanes: each row depends only on its lane class. -/
def LaneFactored {N d : ℕ} {Row : Type*} (rows : Fin N → Row) (lane : Fin N → Fin d) : Prop :=
  ∃ g : Fin d → Row, rows = g ∘ lane

/-- **Lane bound:** a lane-factored sheet has at most `d` distinct rows (profiles). -/
theorem profileCount_le_of_laneFactored {N d : ℕ} {Row : Type*} [DecidableEq Row]
    (rows : Fin N → Row) (lane : Fin N → Fin d) (h : LaneFactored rows lane) :
    (Finset.univ.image rows).card ≤ d := by
  obtain ⟨g, rfl⟩ := h
  have hsub : Finset.univ.image (g ∘ lane) ⊆ Finset.univ.image g := by
    intro x hx; rw [mem_image] at hx ⊢; obtain ⟨i, _, rfl⟩ := hx
    exact ⟨lane i, mem_univ _, rfl⟩
  calc (Finset.univ.image (g ∘ lane)).card
      ≤ (Finset.univ.image g).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_image_le
    _ = d := by rw [Finset.card_univ, Fintype.card_fin]

/-- **The lane-classification core.**  The (Hadamard / pointwise) product of *any number* `m` of sheets that
share the same `d` lanes is itself lane-factored through those `d` lanes — so the product cannot multiply
the lane count.  This is the coupling that defeats the tensor blow-up. -/
theorem laneFactored_prod {N d m : ℕ} {Row : Type*} [CommMonoid Row]
    (lane : Fin N → Fin d) (sheets : Fin m → Fin N → Row) (h : ∀ j, LaneFactored (sheets j) lane) :
    LaneFactored (fun i => ∏ j, sheets j i) lane := by
  choose g hg using h
  refine ⟨fun l => ∏ j, g j l, ?_⟩
  funext i
  simp only [Function.comp_apply, hg, Function.comp_def]

/-- The product of `m` shared-`d`-lane sheets has `≤ d` distinct profiles, **independent of `m`**.  With
`d = poly(n)` lanes this is `poly(n)` rank — the bound `CookLevinFrontierHyp` needs. -/
theorem product_profileCount_le {N d m : ℕ} {Row : Type*} [CommMonoid Row] [DecidableEq Row]
    (lane : Fin N → Fin d) (sheets : Fin m → Fin N → Row) (h : ∀ j, LaneFactored (sheets j) lane) :
    (Finset.univ.image (fun i => ∏ j, sheets j i)).card ≤ d :=
  profileCount_le_of_laneFactored _ lane (laneFactored_prod lane sheets h)

/-- **The lane-classification claim for the Cook–Levin compilation** — the precise open structural lemma:
all `m` sheets factor through the same `d` lanes.  *Not asserted.*  By `product_profileCount_le`, it implies
the product has `≤ d` profiles; with `d = poly(n)` this discharges the counting half of
`CookLevinFrontierHyp`. -/
def CookLevinLaneClassified {N d m : ℕ} {Row : Type*}
    (lane : Fin N → Fin d) (sheets : Fin m → Fin N → Row) : Prop :=
  ∀ j, LaneFactored (sheets j) lane

/-! ### Coupled vs independent product — computed -/

/-- Hadamard (entrywise) product over `F₂` — coupled sheets on the *same* rows/cols (shared variables). -/
def hadamard (A B : List (List Bool)) : List (List Bool) :=
  List.zipWith (fun arow brow => List.zipWith (· && ·) arow brow) A B

/-- Two rank-`2` sheets sharing the same `2` lanes (rows `0,1` = lane `0`; row `2` = lane `1`). -/
def A : List (List Bool) := [[true,true,false],[true,true,false],[false,false,true]]
/-- A second sheet sharing the same lanes. -/
def B : List (List Bool) := [[true,false,true],[true,false,true],[false,true,true]]

theorem A_rank : f2rank A = 2 := by native_decide
theorem B_rank : f2rank B = 2 := by native_decide
/-- Coupled (shared-lane Hadamard) product of two sheets stays `≤ 2` (= #lanes). -/
theorem coupled_stays_bounded : f2rank (hadamard A B) ≤ 2 := by native_decide
/-- Coupled product of `3+` sheets is still `≤ 2` — bounded regardless of #factors. -/
theorem coupled_three_bounded : f2rank (hadamard A (hadamard B (hadamard A B))) ≤ 2 := by native_decide
/-- The *independent* (tensor) product of the same sheets explodes to `4 = 2²`. -/
theorem independent_explodes : f2rank (kron A B) = 4 := by native_decide

end PallLean.Paper93.DeepMath.PathB.LaneClassification

#print axioms PallLean.Paper93.DeepMath.PathB.LaneClassification.product_profileCount_le
