import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugePosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugeNotIdentityN2
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Content-driven gauge bundle bridge

This file packages, into a single 5-fold conjunction, the structural
guarantees for the **content-driven gauge** at `n = 2`:

  1. PosDef on every `2x2` tableau (via
     `contentDrivenGauge_n2_posDef`);
  2. Never the `2x2` identity matrix (via
     `contentDrivenGauge_n2_ne_identity`);
  3. Distinguishability of the underlying coupling between the zero
     and all-ones tableaus at `m = n = 2` (via
     `contentDrivenAlpha_distinguishes`);
  4. Identification of the zero tableau gauge with
     `compiledGadget 1 2` (via `contentDrivenGauge_zero`);
  5. Identification of the all-ones tableau gauge with
     `compiledGadget 5 2` (via `contentDrivenGauge_allOnes`, using
     `1 + 2 * 2 = 5`).

These five facts together exhibit the content-driven gauge as a genuine
positive-definite, content-dependent, non-identity witness anchored to
two named representatives of the §28.3 compiled-gadget family.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Content-driven gauge bundle: 5-fold conjunction at n=2.**

    For any n=2 SAT decider tableau, the content-driven gauge is:
    1. PosDef
    2. NOT the identity matrix
    3. Distinguishable for zero vs all-ones tableaus
    4. Equal to compiledGadget 1 2 for the zero tableau
    5. Equal to compiledGadget 5 2 for the all-ones tableau (m=n=2 case)
-/
theorem contentDrivenGauge_n2_bundle :
    -- (1) For any 2x2 tableau, gauge is PosDef
    (∀ (m : ℕ) (T : SATDeciderTableau m 2), (contentDrivenGauge T).PosDef) ∧
    -- (2) For any 2x2 tableau, gauge is NOT identity
    (∀ (m : ℕ) (T : SATDeciderTableau m 2),
       contentDrivenGauge T ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    -- (3) Different tableaus → different couplings (when m*n ≥ 1)
    (contentDrivenAlpha (SATDeciderTableau.zero 2 2) ≠
     contentDrivenAlpha (SATDeciderTableau.allOnes 2 2)) ∧
    -- (4) Zero tableau gauge = compiledGadget 1 2
    (contentDrivenGauge (SATDeciderTableau.zero 2 2) = compiledGadget 1 2) ∧
    -- (5) All-ones tableau gauge = compiledGadget 5 2
    (contentDrivenGauge (SATDeciderTableau.allOnes 2 2) = compiledGadget 5 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intros m T
    exact contentDrivenGauge_n2_posDef T
  · intros m T
    exact contentDrivenGauge_n2_ne_identity T
  · apply contentDrivenAlpha_distinguishes
    norm_num
  · exact contentDrivenGauge_zero 2 2
  · rw [contentDrivenGauge_allOnes]
    congr 1
    norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid
