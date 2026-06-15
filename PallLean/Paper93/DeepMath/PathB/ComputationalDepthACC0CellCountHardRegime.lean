import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DirectCellConcentration

/-!
# The hard regime — exactly where the open cell-count lemma still lives

Every *proved* route to a collapse on a live set `L` certifies `cellPatternCount supports L < |L|` via one of two
general upper bounds:

* the **survivor/rank** bound `cellPatternCount ≤ 2^{survivingCount}` (so `2^{survivingCount} < |L|` ⇒ collapse), and
* the **direct/global** bound `cellPatternCount ≤ globalCellCount` (so `globalCellCount < |L|` ⇒ collapse).

So a collapse on `L` is *not yet established by either general route* precisely when **both** bounds fail:

```
HardRegime supports L  :=  |L| ≤ 2^{survivingCount supports L}  ∧  |L| ≤ globalCellCount supports.
```

This file pins that regime: outside it the collapse is already proved, and the open lemma
`FullACC0ForcesLowCellCount` reduces to resolving the hard regime alone.  The realistic `ACC⁰` setting — polynomially
many wide gates (`2^{survivingCount} ≥ n`) with all-distinct global patterns (`globalCellCount = n`) — *is* the hard
regime, which is why the structured fragments (laminar, bounded-distinct, low-VC, clustered, sunflower) and the open
merge-concentration are the only ways forward.

## What is proved (clean axioms, no `sorry`)

* `HardRegime supports L` — both general collapse bounds fail on `L`.
* **`collapse_of_not_hardRegime`** — `¬ HardRegime supports L ⇒ CellCountCollapse supports L` (outside the hard regime,
  collapse holds, via the survivor route or the global route).
* **`full_of_hardRegime_resolved`** — `(HardRegime supports univ → FullACC0ForcesLowCellCount supports) ⇒
  FullACC0ForcesLowCellCount supports`: the hard regime is the *only* obstruction.
* **`hardRegime_univ_of`** — the realistic regime `n ≤ 2^{survivingCount univ}`, `n ≤ globalCellCount` *is* hard.

## Honest scope

This is a reduction, not a resolution: it isolates the open content (`cellPatternCount L < |L|` while both general bounds
fail) but does not establish it.  That open content is the structural merge-concentration on the surviving gates
(`NP ⊄ ACC⁰`-strength).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CellCountHardRegime

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountSwitching
open PallLean.Paper93.DeepMath.PathB.ACC0DirectCellConcentration

variable {k n : ℕ}

/-- **The hard regime**: both general collapse bounds fail on `L` — the live set is no larger than `2^{survivingCount}`
*and* no larger than the global pattern count. -/
def HardRegime (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) : Prop :=
  L.card ≤ 2 ^ survivingCount supports L ∧ L.card ≤ globalCellCount supports

/-- **Outside the hard regime, collapse holds (proved).**  If `2^{survivingCount} < |L|` use the survivor/rank route;
if `globalCellCount < |L|` use the direct/global route. -/
theorem collapse_of_not_hardRegime (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (h : ¬ HardRegime supports L) : CellCountCollapse supports L := by
  unfold HardRegime at h
  push_neg at h
  by_cases hA : L.card ≤ 2 ^ survivingCount supports L
  · exact low_global_cellCount_collapse supports L (h hA)
  · push_neg at hA
    exact rank_collapse_implies_cellCount_collapse supports L
      (survivor_collapse_implies_rank_collapse supports L hA)

/-- **The hard regime is the only obstruction (proved).**  If the open lemma holds whenever `supports` is hard on the
full cube, then it holds outright — because if `supports` is *not* hard on the cube, the collapse is already there. -/
theorem full_of_hardRegime_resolved (supports : Fin k → Finset (Fin n))
    (h : HardRegime supports Finset.univ → FullACC0ForcesLowCellCount supports) :
    FullACC0ForcesLowCellCount supports := by
  by_cases hh : HardRegime supports Finset.univ
  · exact h hh
  · exact ⟨Finset.univ, collapse_of_not_hardRegime supports Finset.univ hh⟩

/-- **The realistic regime is hard (proved).**  Polynomially many wide gates (`n ≤ 2^{survivingCount univ}`) with
all-distinct global patterns (`n ≤ globalCellCount`) put the full cube in the hard regime. -/
theorem hardRegime_univ_of (supports : Fin k → Finset (Fin n))
    (h1 : n ≤ 2 ^ survivingCount supports Finset.univ) (h2 : n ≤ globalCellCount supports) :
    HardRegime supports Finset.univ := by
  have hc : (Finset.univ : Finset (Fin n)).card = n := by simp
  unfold HardRegime
  rw [hc]
  exact ⟨h1, h2⟩

end PallLean.Paper93.DeepMath.PathB.ACC0CellCountHardRegime

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCountHardRegime.collapse_of_not_hardRegime
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCountHardRegime.full_of_hardRegime_resolved
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CellCountHardRegime.hardRegime_univ_of
