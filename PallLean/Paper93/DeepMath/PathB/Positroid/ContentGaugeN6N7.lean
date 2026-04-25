import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugePosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugeNotIdentityN2
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Non-trivial content-driven gauges at `n = 6` and `n = 7`

This file extends the content-driven gauge non-triviality results
from `ContentGaugePosDef.lean` and `ContentGaugeNotIdentityN2.lean`
to the cases `n = 6` and `n = 7`, mirroring the pattern in
`ContentGaugeN4N5NonTrivial.lean`.

For each `n ≥ 1`, the content-driven gauge `contentDrivenGauge T` is
`PosDef` (because `contentDrivenAlpha T ≥ 1 > 0`), and for each
`n ≥ 2` it is genuinely non-identity (via the structural argument in
`CompiledGadgetNonIdentityAny.lean`).

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- Content-driven gauge at n=6 is PosDef and non-identity for any tableau. -/
theorem contentDrivenGauge_n6_nontrivial {m : ℕ} (T : SATDeciderTableau m 6) :
    (contentDrivenGauge T).PosDef ∧
    contentDrivenGauge T ≠ (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
  refine ⟨?_, ?_⟩
  · exact contentDrivenGauge_posDef T (by norm_num : 1 ≤ 6)
  · exact contentDrivenGauge_ne_identity_general T (by norm_num : 2 ≤ 6)

/-- Content-driven gauge at n=7 is PosDef and non-identity for any tableau. -/
theorem contentDrivenGauge_n7_nontrivial {m : ℕ} (T : SATDeciderTableau m 7) :
    (contentDrivenGauge T).PosDef ∧
    contentDrivenGauge T ≠ (1 : Matrix (Fin 7) (Fin 7) ℝ) := by
  refine ⟨?_, ?_⟩
  · exact contentDrivenGauge_posDef T (by norm_num : 1 ≤ 7)
  · exact contentDrivenGauge_ne_identity_general T (by norm_num : 2 ≤ 7)

end PallLean.Paper93.DeepMath.PathB.Positroid
