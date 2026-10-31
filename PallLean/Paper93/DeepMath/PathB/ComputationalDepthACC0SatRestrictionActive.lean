import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SatSurvivorCells
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCSwitchingPipeline

/-!
# Restriction ⇒ few active gates ⇒ few cells

`…ACC0SatSurvivorCells` proved `#cells ≤ (n+1)^{#active}`.  This file connects the **restriction pipeline** directly
to `#active`: after restricting to a live set `L`, the restricted support family `S_j ∩ L` is *active* at `j`
exactly when `S_j ∩ L ≠ ∅`, i.e. when `S_j` **survives** (`¬ Disjoint (S_j) L`).  So the active count of the
restricted family **equals the surviving count**, and the cell bound becomes `#cells ≤ (n+1)^{#surviving}`.

This is the bridge from the survivor machinery (`survivingCount`, controlled by `…ACCSwitchingPipeline`,
`…ACCCoreDecomposition`, `…ACCRestrictionTree`) to the SAT‑speedup cell cost.

## What is proved (clean axioms, no `sorry`)

* `activeSupports_restrict` — `activeSupports (S· ∩ L) = {j : ¬ Disjoint (S_j) L}` (active after restriction =
  surviving).
* `activeSupports_restrict_card` — `#active (S· ∩ L) = survivingCount`.
* `cells_restrict_le_surviving` — **`#cells(S· ∩ L) ≤ (n+1)^{survivingCount}`**: the restricted cell count is
  governed by the surviving gate count.

## Honest scope

The genuine link between the restriction/survivor machinery and the speedup cell cost.  Still the cell‑search cost
model; proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SatRestrictionActive

open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0SatSurvivorCells
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline

variable {n k : ℕ}

/-- **Active after restriction = surviving (proved).** -/
theorem activeSupports_restrict (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) :
    activeSupports (fun j => supports j ∩ L)
      = Finset.univ.filter (fun j => ¬ Disjoint (supports j) L) := by
  unfold activeSupports
  apply Finset.filter_congr
  intro j _
  rw [ne_eq, Finset.disjoint_iff_inter_eq_empty]

/-- **The active count of the restricted family equals the surviving count (proved).** -/
theorem activeSupports_restrict_card (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) :
    (activeSupports (fun j => supports j ∩ L)).card = survivingCount supports L := by
  rw [activeSupports_restrict]; rfl

/-- **Restriction ⇒ few cells (proved): `#cells(S· ∩ L) ≤ (n+1)^{survivingCount}`.** -/
theorem cells_restrict_le_surviving (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) :
    (Finset.univ.image (weightVec (fun j => supports j ∩ L))).card
      ≤ (n + 1) ^ survivingCount supports L := by
  rw [← activeSupports_restrict_card]
  exact image_card_le_active (fun j => supports j ∩ L)

end PallLean.Paper93.DeepMath.PathB.ACC0SatRestrictionActive

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatRestrictionActive.activeSupports_restrict_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatRestrictionActive.cells_restrict_le_surviving
