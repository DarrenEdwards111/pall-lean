import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RankBridge

/-!
# The direct cell-count route — the sharpest observer collapse (cells, not rank)

The rank route bounds the number of observer cells by `2^{cellRank}`.  But rank still overestimates some structured
systems.  The *actual* governing quantity is the **number of distinct cell patterns**, and the collapse argument
needs only that this is below `|L|`.  This file makes that direct route explicit:

```
cellPatternCount supports L < |L|  ⇒  same-cell pair  ⇒  witness  ⇒  low holonomy correlation
```

It **strictly generalizes** the rank route, since `cellPatternCount ≤ 2^{cellRank}`
(`…ACC0RankBridge.cellPattern_image_card_le`): a rank collapse is a special case of a cell-count collapse.

## What is proved (clean axioms, no `sorry`)

* `cellPatternImage` / `cellPatternCount` — the realized cell patterns over `L` and their number;
  `CellCountCollapse supports L := cellPatternCount supports L < |L|`.
* **`exists_sameCell_pair_of_count`** — `CellCountCollapse` ⇒ two distinct live coordinates share a cell (the bare
  pigeonhole, no rank bound).
* **`cellCountCollapse_implies_low_correlation`** — `CellCountCollapse ⇒ LowHolonomyCorrelation`.
* **`rank_collapse_implies_cellCount_collapse`** — `2^{cellRank} < |L| ⇒ CellCountCollapse`: rank collapse is a
  cell-count collapse, so this route subsumes the rank route.

## Honest scope

This is the sharpest form of the observer collapse — cells, not rank.  The full open target sharpens accordingly to
`ACC0ForcesLowCellCount` (`∃ L, cellPatternCount supports L < |L|`), which is `≤` the rank version.  Forcing few cell
patterns for general `ACC⁰` under a restriction remains the open `NP ⊄ ACC⁰`-strength lemma.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge

variable {k n : ℕ}

/-- The set of cell patterns realized by the live coordinates `L`. -/
def cellPatternImage (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) :
    Finset (Fin k → ZMod 2) :=
  L.image (cellPatternVec supports)

/-- The number of distinct observer cells over `L` — the true governing quantity. -/
def cellPatternCount (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) : ℕ :=
  (cellPatternImage supports L).card

/-- **Cell-count collapse**: fewer observer cells than live coordinates. -/
def CellCountCollapse (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) : Prop :=
  cellPatternCount supports L < L.card

/-- **The bare pigeonhole (proved): `CellCountCollapse` ⇒ two live coordinates share a cell.** -/
theorem exists_sameCell_pair_of_count (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (h : CellCountCollapse supports L) :
    ∃ v ∈ L, ∃ w ∈ L, v ≠ w ∧ SameCell supports v w := by
  obtain ⟨v, hv, w, hw, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to h
      (fun v hv => Finset.mem_image_of_mem _ hv)
  exact ⟨v, hv, w, hw, hne, (sameCell_iff_pattern supports v w).mpr heq⟩

/-- **The direct cell-count bridge (proved): `CellCountCollapse ⇒ low holonomy correlation`.** -/
theorem cellCountCollapse_implies_low_correlation (supports : Fin k → Finset (Fin n))
    (g : (Fin k → ℕ) → Bool) (L : Finset (Fin n)) (h : CellCountCollapse supports L) :
    LowHolonomyCorrelation supports g := by
  obtain ⟨v, _, w, _, hne, hcell⟩ := exists_sameCell_pair_of_count supports L h
  obtain ⟨vv, ww, hvw, hb⟩ := cellWitness_gives_low_correlation supports {v} g
    ⟨v, w, hne, Finset.mem_singleton_self v,
      fun hmem => hne (Finset.mem_singleton.mp hmem).symm, hcell⟩
  exact ⟨{v}, vv, ww, hvw, hb⟩

/-- **Rank collapse is a cell-count collapse (proved): the cell-count route subsumes the rank route.** -/
theorem rank_collapse_implies_cellCount_collapse (supports : Fin k → Finset (Fin n))
    (L : Finset (Fin n)) (h : 2 ^ cellRank supports L < L.card) : CellCountCollapse supports L :=
  lt_of_le_of_lt (cellPattern_image_card_le supports L) h

end PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute.exists_sameCell_pair_of_count
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute.cellCountCollapse_implies_low_correlation
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute.rank_collapse_implies_cellCount_collapse
