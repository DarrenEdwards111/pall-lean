import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenAlpha
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy

/-!
# Content-driven gauge depending on tableau entries

This file builds a **content-driven gauge witness** by feeding the
content-driven coupling `contentDrivenAlpha T` (which depends on the
tableau's actual entries via `tableauTraceCoupling`) into the §28.3
canonical compiled gadget `compiledGadget`.

The resulting matrix `contentDrivenGauge T` therefore genuinely depends
on the tableau's content, not merely on its dimension.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.PathB

/-- A **content-driven gauge witness** built from the §28.3 compiled gadget at the
    content-driven coupling. The coupling depends on the tableau's actual entries
    (via `contentDrivenAlpha`), so this matrix genuinely depends on the tableau's
    content (not just its dimension). -/
noncomputable def contentDrivenGauge {m n : ℕ}
    (T : SATDeciderTableau m n) : Matrix (Fin n) (Fin n) ℝ :=
  compiledGadget (contentDrivenAlpha T) n

/-- The content-driven gauge for the zero tableau equals compiledGadget 1 n. -/
theorem contentDrivenGauge_zero (m n : ℕ) :
    contentDrivenGauge (SATDeciderTableau.zero m n) = compiledGadget 1 n := by
  unfold contentDrivenGauge
  rw [contentDrivenAlpha_zero]

/-- The content-driven gauge for the all-ones tableau equals compiledGadget (1+m*n) n. -/
theorem contentDrivenGauge_allOnes (m n : ℕ) :
    contentDrivenGauge (SATDeciderTableau.allOnes m n) =
      compiledGadget (1 + (m : ℝ) * n) n := by
  unfold contentDrivenGauge
  rw [contentDrivenAlpha_allOnes]

/-- For zero vs all-ones tableaus with m*n ≥ 1, the content-driven gauges have
    different couplings. -/
theorem contentDrivenGauge_couplings_distinguish (m n : ℕ) (h : 1 ≤ m * n) :
    contentDrivenAlpha (SATDeciderTableau.zero m n) ≠
    contentDrivenAlpha (SATDeciderTableau.allOnes m n) :=
  contentDrivenAlpha_distinguishes m n h

/-- The content-driven coupling is positive for any tableau, so the gauge is well-defined. -/
theorem contentDrivenGauge_coupling_pos {m n : ℕ} (T : SATDeciderTableau m n) :
    0 < contentDrivenAlpha T :=
  contentDrivenAlpha_pos T

end PallLean.Paper93.DeepMath.PathB.Positroid
