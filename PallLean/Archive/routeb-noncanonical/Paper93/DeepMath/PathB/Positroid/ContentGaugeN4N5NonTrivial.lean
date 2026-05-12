import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugePosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugeNotIdentityN2
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Non-trivial content-driven gauges at `n = 4` and `n = 5`

This file extends the content-driven gauge non-triviality results
from `ContentGaugePosDef.lean` and `ContentGaugeNotIdentityN2.lean`
to the cases `n = 4` and `n = 5`, and packages a combined statement
covering `n ∈ {2, 3, 4, 5}` along with the fully general
`n ≥ 2` non-identity statement.

For each `n ≥ 1`, the content-driven gauge `contentDrivenGauge T` is
`PosDef` (because `contentDrivenAlpha T ≥ 1 > 0`), and for each
`n ≥ 2` it is genuinely non-identity (via the structural argument in
`CompiledGadgetNonIdentityAny.lean`). The four small cases
`n = 2, 3, 4, 5` are bundled together for downstream use.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- Content-driven gauge at n=4 is PosDef and non-identity for any tableau. -/
theorem contentDrivenGauge_n4_nontrivial {m : ℕ} (T : SATDeciderTableau m 4) :
    (contentDrivenGauge T).PosDef ∧
    contentDrivenGauge T ≠ (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  refine ⟨?_, ?_⟩
  · exact contentDrivenGauge_posDef T (by norm_num : 1 ≤ 4)
  · exact contentDrivenGauge_ne_identity_general T (by norm_num : 2 ≤ 4)

/-- Content-driven gauge at n=5 is PosDef and non-identity for any tableau. -/
theorem contentDrivenGauge_n5_nontrivial {m : ℕ} (T : SATDeciderTableau m 5) :
    (contentDrivenGauge T).PosDef ∧
    contentDrivenGauge T ≠ (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
  refine ⟨?_, ?_⟩
  · exact contentDrivenGauge_posDef T (by norm_num : 1 ≤ 5)
  · exact contentDrivenGauge_ne_identity_general T (by norm_num : 2 ≤ 5)

/-- Combined statement at n=2,3,4,5: content-driven gauge is PosDef and non-identity. -/
theorem content_driven_nontrivial_n2_to_n5 :
    (∀ (m : ℕ) (T : SATDeciderTableau m 2),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∀ (m : ℕ) (T : SATDeciderTableau m 3),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ)) ∧
    (∀ (m : ℕ) (T : SATDeciderTableau m 4),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 4) (Fin 4) ℝ)) ∧
    (∀ (m : ℕ) (T : SATDeciderTableau m 5),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 5) (Fin 5) ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros m T
    exact ⟨contentDrivenGauge_n2_posDef T, contentDrivenGauge_n2_ne_identity T⟩
  · intros m T
    exact ⟨contentDrivenGauge_n3_posDef T, contentDrivenGauge_n3_ne_identity T⟩
  · intros m T
    exact contentDrivenGauge_n4_nontrivial T
  · intros m T
    exact contentDrivenGauge_n5_nontrivial T

/-- For ALL n ≥ 2 tableaus, the content-driven gauge is non-identity. -/
theorem content_driven_nontrivial_general {m n : ℕ} (T : SATDeciderTableau m n) (hn : 2 ≤ n) :
    contentDrivenGauge T ≠ (1 : Matrix (Fin n) (Fin n) ℝ) :=
  contentDrivenGauge_ne_identity_general T hn

end PallLean.Paper93.DeepMath.PathB.Positroid
