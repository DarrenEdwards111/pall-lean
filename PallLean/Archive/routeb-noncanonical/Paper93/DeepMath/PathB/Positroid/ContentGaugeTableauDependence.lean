import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenAlpha
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Tableau-content dependence of the content-driven gauge

This file collects the **content-dependence theorems** for the
content-driven gauge `contentDrivenGauge` and its coupling
`contentDrivenAlpha`.

Concretely, we record:
- the explicit value `contentDrivenAlpha (zero m n) = 1`,
- the explicit value `contentDrivenAlpha (allOnes m n) = 1 + m*n`,
- the resulting compiled-gadget identifications at `m=n=2`,
- and the distinguishing inequality at `m=n=2` (so `m*n = 4 ≥ 1`).

These together show that the content-driven gauge `contentDrivenGauge`
genuinely depends on the tableau's content (not merely on its
dimensions), since the underlying coupling differs between the zero and
all-ones tableaus once `m*n ≥ 1`.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- For zero vs all-ones tableaus at m=n=2 (so m*n = 4 ≥ 1), the content-driven
    gauges have different couplings. -/
theorem contentDrivenGauge_n2_distinguishes :
    contentDrivenAlpha (SATDeciderTableau.zero 2 2) ≠
    contentDrivenAlpha (SATDeciderTableau.allOnes 2 2) := by
  apply contentDrivenAlpha_distinguishes
  norm_num

/-- The content-driven gauge for the zero 2x2 tableau is `compiledGadget 1 2`. -/
theorem contentDrivenGauge_zero_2x2 :
    contentDrivenGauge (SATDeciderTableau.zero 2 2) = compiledGadget 1 2 :=
  contentDrivenGauge_zero 2 2

/-- The content-driven gauge for the all-ones 2x2 tableau is `compiledGadget 5 2`. -/
theorem contentDrivenGauge_allOnes_2x2 :
    contentDrivenGauge (SATDeciderTableau.allOnes 2 2) = compiledGadget (1 + 4) 2 := by
  rw [contentDrivenGauge_allOnes]
  congr 1
  norm_num

/-- For zero tableau, the content-driven coupling is exactly 1. -/
theorem contentDrivenAlpha_zero_eq_one (m n : ℕ) :
    contentDrivenAlpha (SATDeciderTableau.zero m n) = 1 :=
  contentDrivenAlpha_zero m n

/-- For all-ones m×n tableau, the content-driven coupling is exactly 1 + m*n. -/
theorem contentDrivenAlpha_allOnes_eq (m n : ℕ) :
    contentDrivenAlpha (SATDeciderTableau.allOnes m n) = 1 + (m : ℝ) * n :=
  contentDrivenAlpha_allOnes m n

end PallLean.Paper93.DeepMath.PathB.Positroid
