import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellCountRoute

/-!
# Rank-cell collapse — the linear observer state space is *exactly* `2^{rank}`

The survivor-count observer is too crude for wide overlapping `MOD` supports (they survive restrictions badly).  The
right linear-algebraic invariant is the **cell rank** — the `F₂`-dimension of the span of the realized cell patterns —
because the observer's *state space* is the span `cellSpan`, whose size is **exactly** `2^{cellRank}` (not merely
bounded by `2^{survivingCount}`).  This file crystallises that and packages the rank route's collapse bridge.

```
|cellSpan supports L|  =  2^{cellRank supports L}          (the observer state space, exactly)
RankCellCollapse supports L := 2^{cellRank supports L} < |L|   ⇒   low holonomy correlation.
```

## What is proved (clean axioms, no `sorry`)

* **`observer_state_space_card`** — `|cellSpan supports L| = 2^{cellRank supports L}`: the linear observer state space
  has *exactly* `2^{rank}` states (over `F₂`, via `Module.card_eq_pow_finrank`).
* `RankCellCollapse` — the rank collapse predicate `2^{cellRank} < |L|`.
* **`cellPatternCount_le_observer_states`** — the realized cells number `≤ |cellSpan| = 2^{cellRank}`.
* **`rank_cell_collapse_implies_low_holonomy_correlation`** — `RankCellCollapse ⇒ LowHolonomyCorrelation`, directly
  (the cell count is `2^{rank}`, never going through the cruder survivor count).

## Honest scope

The rank bridge is the right linear-algebraic upgrade of the observer route (and the fragments — bounded-overlap,
laminar, low support-span, clustered — and the subadditive composition `cellRank_append_le` / budgeted lift are already
in the corpus).  The genuinely open content is the **rank-shrink-under-restriction** lemma for wide overlapping `MOD`:
that some boundary/restriction forces `cellRank < log₂|L|` on a large live set.  That is the rank analogue of the
`MOD` wall (no absorbing value), and remains the `NP ⊄ ACC⁰`-strength frontier.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RankCellCollapse

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute

variable {k n : ℕ}

/-- **The observer state space has exactly `2^{cellRank}` states (proved).**  `cellSpan` is an `F₂`-subspace of
dimension `cellRank`, so it has exactly `2^{cellRank}` elements — the true (linear) observer-state count, sharper than
the `2^{survivingCount}` row-count bound. -/
theorem observer_state_space_card (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) :
    Nat.card ↥(cellSpan supports L) = 2 ^ cellRank supports L := by
  haveI : Fintype ↥(cellSpan supports L) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, cellRank, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- **Rank-cell collapse**: fewer observer states (`2^{cellRank}`) than live coordinates. -/
def RankCellCollapse (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) : Prop :=
  2 ^ cellRank supports L < L.card

/-- **The realized cells number at most the observer state count (proved): `≤ |cellSpan| = 2^{cellRank}`.** -/
theorem cellPatternCount_le_observer_states (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) :
    cellPatternCount supports L ≤ Nat.card ↥(cellSpan supports L) := by
  rw [observer_state_space_card]
  exact cellPattern_image_card_le supports L

/-- **The rank-cell bridge (proved): `RankCellCollapse ⇒ low holonomy correlation`, directly.**  When the linear
observer has fewer than `|L|` states, two live coordinates share a cell and the involution engine defeats the
predictor — bypassing the survivor count entirely. -/
theorem rank_cell_collapse_implies_low_holonomy_correlation (supports : Fin k → Finset (Fin n))
    (g : (Fin k → ℕ) → Bool) (L : Finset (Fin n)) (h : RankCellCollapse supports L) :
    LowHolonomyCorrelation supports g :=
  rank_collapse_low_correlation supports g L h

/-- **Rank-cell collapse is a cell-count collapse (proved): the rank route refines the cell-count route.** -/
theorem rankCellCollapse_implies_cellCountCollapse (supports : Fin k → Finset (Fin n))
    (L : Finset (Fin n)) (h : RankCellCollapse supports L) : CellCountCollapse supports L :=
  rank_collapse_implies_cellCount_collapse supports L h

end PallLean.Paper93.DeepMath.PathB.ACC0RankCellCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankCellCollapse.observer_state_space_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankCellCollapse.cellPatternCount_le_observer_states
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankCellCollapse.rank_cell_collapse_implies_low_holonomy_correlation
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankCellCollapse.rankCellCollapse_implies_cellCountCollapse
