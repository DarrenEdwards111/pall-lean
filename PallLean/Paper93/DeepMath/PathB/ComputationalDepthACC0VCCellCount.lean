import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ChainCellCount
import Mathlib.Combinatorics.SetFamily.Shatter

/-!
# Low VC dimension ⇒ few observer cells (Sauer–Shelah) — the natural generalization of the solved fragments

The cell pattern of a coordinate `v` is the indicator of its **gate-membership set** `suppSet v = {j : v ∈ supports j}
⊆ Fin k`.  So the number of distinct observer cells is exactly the size of the set family

```
patternFamily = { suppSet v : v ∈ L }  ⊆  2^{Fin k},
```

and bounding it is a pure set-family question.  By the **Sauer–Shelah lemma** (`Finset.card_shatterer_le_sum_vcDim`
in Mathlib, via Pajor's `card_le_card_shatterer`), if this family has VC dimension `≤ d` then it realizes at most
`∑_{i ≤ d} C(k, i)` distinct cells — a polynomial in the gate count `k` of degree `d`, with **no reference to rank**.

This is exactly the N-Frame observer idea — *few observer patterns, not necessarily low rank* — and it is the common
generalization of the solved fragments (bounded-distinct, equal/low-span, clustered, laminar all have small VC).
Collapse follows whenever `∑_{i ≤ d} C(k, i) < |L|`.

## What is proved (clean axioms, no `sorry`)

* `cellVCdim supports L` := the VC dimension of the gate-membership family `{suppSet v : v ∈ L}`.
* **`patternFamily_card`** — `|{suppSet v : v ∈ L}| = cellPatternCount supports L` (the family size *is* the cell count;
  the one-set map is a bijection between patterns and their gate-membership sets).
* **`lowVC_cellPatternCount_le`** — `cellVCdim supports L ≤ d ⇒ cellPatternCount supports L ≤ ∑_{i ≤ d} C(k, i)`
  (Pajor `+` Sauer–Shelah).
* **`lowVC_cellCountCollapse`** / **`lowVC_low_correlation`** — `∑_{i ≤ d} C(k, i) < |L| ⇒` collapse ⇒ low correlation.

## Honest scope

A genuine new fragment subsuming the earlier ones: it asks only for bounded *VC dimension* of the gate-membership
family, not low rank or few distinct supports.  But the open lemma `ACC0ForcesLowCellCount` requires *low VC under a
restriction* for the family arising from general poly-many wide overlapping `MOD` supports — and bounding that VC
dimension is exactly the open structural-concentration content (`NP ⊄ ACC⁰`-strength).  This fragment converts the
problem to "bound the observer VC dimension"; it does not bound it for the hard regime.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0VCCellCount

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute
open PallLean.Paper93.DeepMath.PathB.ACC0ChainCellCount

variable {k n : ℕ}

/-- The **observer VC dimension**: the VC dimension of the gate-membership family `{suppSet v : v ∈ L}`. -/
def cellVCdim (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) : ℕ :=
  (L.image (suppSet supports)).vcDim

/-- **The gate-membership family size *is* the cell count (proved).**  The one-set map `p ↦ {j : p j = 1}` is a
bijection between cell patterns and gate-membership sets, so the two image cardinalities agree. -/
theorem patternFamily_card (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) :
    (L.image (suppSet supports)).card = cellPatternCount supports L := by
  have hfun : suppSet supports
      = (fun p : Fin k → ZMod 2 => Finset.univ.filter (fun j => p j = 1)) ∘ (cellPatternVec supports) := by
    funext v
    simp only [Function.comp_apply]
    exact (oneSet_eq_suppSet supports v).symm
  unfold cellPatternCount cellPatternImage
  rw [hfun, ← Finset.image_image]
  apply Finset.card_image_of_injOn
  intro p hp p' hp' hpp
  rw [Finset.mem_coe, Finset.mem_image] at hp hp'
  obtain ⟨v, _, rfl⟩ := hp
  obtain ⟨w, _, rfl⟩ := hp'
  simp only [oneSet_eq_suppSet] at hpp
  exact cellPatternVec_eq_of_suppSet supports v w hpp

/-- **Low VC dimension ⇒ few cells (proved): Sauer–Shelah.**  If the observer VC dimension is `≤ d`, the cell count is
at most `∑_{i ≤ d} C(k, i)` — a degree-`d` polynomial in the gate count, with no rank hypothesis. -/
theorem lowVC_cellPatternCount_le (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) (d : ℕ)
    (hvc : cellVCdim supports L ≤ d) :
    cellPatternCount supports L ≤ ∑ i ∈ Finset.Iic d, k.choose i := by
  rw [← patternFamily_card supports L]
  calc (L.image (suppSet supports)).card
      ≤ (L.image (suppSet supports)).shatterer.card := Finset.card_le_card_shatterer _
    _ ≤ ∑ i ∈ Finset.Iic (L.image (suppSet supports)).vcDim, (Fintype.card (Fin k)).choose i :=
        Finset.card_shatterer_le_sum_vcDim
    _ = ∑ i ∈ Finset.Iic (cellVCdim supports L), k.choose i := by
        rw [Fintype.card_fin]; rfl
    _ ≤ ∑ i ∈ Finset.Iic d, k.choose i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr hvc)
        intro i _ _
        exact Nat.zero_le _

/-- **Low VC dimension forces cell collapse (proved): `∑_{i ≤ d} C(k, i) < |L|`.** -/
theorem lowVC_cellCountCollapse (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) (d : ℕ)
    (hvc : cellVCdim supports L ≤ d) (hlt : (∑ i ∈ Finset.Iic d, k.choose i) < L.card) :
    CellCountCollapse supports L :=
  lt_of_le_of_lt (lowVC_cellPatternCount_le supports L d hvc) hlt

/-- **Low VC dimension ⇒ low holonomy correlation (proved).**  The observer fails to correlate whenever the
Sauer–Shelah cell bound drops below the live-set size. -/
theorem lowVC_low_correlation (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool)
    (L : Finset (Fin n)) (d : ℕ) (hvc : cellVCdim supports L ≤ d)
    (hlt : (∑ i ∈ Finset.Iic d, k.choose i) < L.card) :
    LowHolonomyCorrelation supports g :=
  cellCountCollapse_implies_low_correlation supports g L
    (lowVC_cellCountCollapse supports L d hvc hlt)

end PallLean.Paper93.DeepMath.PathB.ACC0VCCellCount

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0VCCellCount.patternFamily_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0VCCellCount.lowVC_cellPatternCount_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0VCCellCount.lowVC_cellCountCollapse
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0VCCellCount.lowVC_low_correlation
