import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NFrameLowerBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellCountRoute

/-!
# The full ACC⁰ cell-count socket — the sharpest (weakest, most achievable) N-Frame switching socket

This packages the cell-count route as a single conditional theorem, beside the survivor socket
(`…ACC0NFrameLowerBound`) and Williams (`…ACC0WilliamsCashout`).  The N-Frame holonomy lower bound reduces to **one**
socket — *forcing few observer cells* — because its other half (few cells ⇒ low correlation) is already a *proved*
theorem (`…ACC0CellCountRoute.cellCountCollapse_implies_low_correlation`).

```
FullACC0ForcesLowCellCount supports   (every predictor forces few cells on some live set — the open switching socket)
        │  nframe_cellcount_route   (PROVED, the cell-count bridge)
        ▼
LowHolonomyCorrelation supports g     (the predictor cannot correlate with some holonomy parity)
```

The cell-count socket is the **sharpest** form: since `cellPatternCount ≤ 2^{cellRank} ≤ 2^{survivingCount}`, it is
*implied by* the survivor socket (`FullACC0ForcesCellCollapse`) and the rank socket — so it is the weakest, most
achievable hypothesis that still yields the holonomy lower bound.  `cellCollapse_implies_lowCellCount` proves this
implication, so every existing discharge of the survivor socket (disjoint, bounded fragments) discharges this one too.

## What is proved (clean axioms, no `sorry`)

* `FullACC0ForcesLowCellCount` — the switching socket: `∃ L, cellPatternCount supports L < |L|`.
* **`nframe_cellcount_route`** — the conditional: `FullACC0ForcesLowCellCount ⇒ LowHolonomyCorrelation` (socket ▸ proved bridge).
* **`cellCollapse_implies_lowCellCount`** — the survivor socket implies the cell-count socket (it is the weakest socket).
* **`NFrameLowCellCount`** / **`nframe_cellcount_lower_bound`** — over a predictor class, the socket ⇒ `ACC0HolonomyLowerBound`.
* **`nframe_lowCellCount_of_cellCollapse`** — the survivor class-socket implies the cell-count class-socket (so the
  conditional is *not vacuous*: every disjoint/bounded discharge of `NFrameCellCollapse` discharges this one).

## Honest scope

`FullACC0ForcesLowCellCount` is the open, `NP ⊄ ACC⁰`-strength switching socket — the sharpest version of the
restriction lemma (`∃ L, cellPatternCount supports L < |L|`).  This file pins and packages it; it does **not** prove
the socket, which is *false for arbitrary support systems* (polynomially many wide overlapping supports give many
distinct cells on every large live set).  The genuine open content is few cells for support systems from *real* `ACC⁰`
circuits *under a restriction*.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CellCountSwitching

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute
open PallLean.Paper93.DeepMath.PathB.ACC0NFrameLowerBound

variable {n : ℕ}

/-- **The cell-count switching socket (the open content).**  A full-`ACC⁰` predictor's supports force *few observer
cells* on some live set — fewer distinct cell patterns than live coordinates.  The sharpest version of the N-Frame
restriction lemma. -/
def FullACC0ForcesLowCellCount {k : ℕ} (supports : Fin k → Finset (Fin n)) : Prop :=
  ∃ L : Finset (Fin n), CellCountCollapse supports L

/-- **The cell-count route as one conditional (proved): the socket cashes out to low correlation.**  Given the
restriction lemma `FullACC0ForcesLowCellCount`, the predictor fails to correlate with the holonomy parity — by the
proved cell-count bridge. -/
theorem nframe_cellcount_route {k : ℕ} (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool)
    (h : FullACC0ForcesLowCellCount supports) : LowHolonomyCorrelation supports g := by
  obtain ⟨L, hL⟩ := h
  exact cellCountCollapse_implies_low_correlation supports g L hL

/-- **The cell-count socket is the weakest (proved): the survivor socket implies it.**  Since
`cellPatternCount ≤ 2^{cellRank} ≤ 2^{survivingCount}`, a survivor collapse on `L` is a cell-count collapse on `L`. -/
theorem cellCollapse_implies_lowCellCount {k : ℕ} (supports : Fin k → Finset (Fin n))
    (h : FullACC0ForcesCellCollapse supports) : FullACC0ForcesLowCellCount supports := by
  obtain ⟨L, hL⟩ := h
  exact ⟨L, rank_collapse_implies_cellCount_collapse supports L
    (survivor_collapse_implies_rank_collapse supports L hL)⟩

/-- **The cell-count switching socket over a predictor class.**  Every predictor forces few cells on some live set. -/
def NFrameLowCellCount {ι : Type} (sys : PredictorClass ι n) : Prop :=
  ∀ i, FullACC0ForcesLowCellCount (sys i).2

/-- **The N-Frame cell-count route as one conditional theorem (proved): socket ⇒ holonomy lower bound.**  The
cell-count analogue of `nframe_acc_lower_bound`, with the *sharpest* (weakest) socket. -/
theorem nframe_cellcount_lower_bound {ι : Type} (sys : PredictorClass ι n)
    (tops : ∀ i, (Fin (sys i).1 → ℕ) → Bool) (h : NFrameLowCellCount sys) :
    ACC0HolonomyLowerBound sys tops :=
  fun i => nframe_cellcount_route (sys i).2 (tops i) (h i)

/-- **The cell-count class-socket is implied by the survivor class-socket (proved): not vacuous.**  Every discharge of
`NFrameCellCollapse` (disjoint supports, bounded fragments) discharges `NFrameLowCellCount`, hence the holonomy lower
bound, via `nframe_cellcount_lower_bound`. -/
theorem nframe_lowCellCount_of_cellCollapse {ι : Type} (sys : PredictorClass ι n)
    (h : NFrameCellCollapse sys) : NFrameLowCellCount sys :=
  fun i => cellCollapse_implies_lowCellCount (sys i).2 (h i)

end PallLean.Paper93.DeepMath.PathB.ACC0CellCountSwitching

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCountSwitching.nframe_cellcount_route
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCountSwitching.cellCollapse_implies_lowCellCount
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCountSwitching.nframe_cellcount_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCountSwitching.nframe_lowCellCount_of_cellCollapse
