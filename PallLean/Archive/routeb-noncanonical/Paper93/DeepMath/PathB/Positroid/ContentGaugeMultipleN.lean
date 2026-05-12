import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugePosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugeNotIdentityN2
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Content-driven gauge non-trivial results bundled across `n = 2..7`

This file bundles together the **non-trivial content-driven gauge**
results from `ContentGaugePosDef.lean` and
`ContentGaugeNotIdentityN2.lean` (and their `n = 4,5,6,7` extensions in
`ContentGaugeN4N5NonTrivial.lean` and `ContentGaugeN6N7.lean`) into a
single packaged theorem.

For every `n ≥ 2` and every `SATDeciderTableau m n`, the content-driven
gauge `contentDrivenGauge T` is simultaneously
- positive definite (because `contentDrivenAlpha T ≥ 1 > 0`), and
- distinct from the identity (via the structural argument in
  `CompiledGadgetNonIdentityAny.lean`).

We provide both a uniform statement
`content_driven_gauge_nontrivial_for_each_n` and a packaged conjunction
`content_driven_gauge_at_n_le_7` covering the small cases used in the
Path B / Positroid development.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem content_driven_gauge_nontrivial_for_each_n (n : ℕ) (hn : 2 ≤ n)
    {m : ℕ} (T : SATDeciderTableau m n) :
    (contentDrivenGauge T).PosDef ∧
    contentDrivenGauge T ≠ (1 : Matrix (Fin n) (Fin n) ℝ) := by
  refine ⟨?_, ?_⟩
  · exact contentDrivenGauge_posDef T (by omega : 1 ≤ n)
  · exact contentDrivenGauge_ne_identity_general T hn

theorem content_driven_gauge_at_n_le_7 :
    (∀ {m : ℕ} (T : SATDeciderTableau m 2),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∀ {m : ℕ} (T : SATDeciderTableau m 3),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ)) ∧
    (∀ {m : ℕ} (T : SATDeciderTableau m 4),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 4) (Fin 4) ℝ)) ∧
    (∀ {m : ℕ} (T : SATDeciderTableau m 5),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 5) (Fin 5) ℝ)) ∧
    (∀ {m : ℕ} (T : SATDeciderTableau m 6),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 6) (Fin 6) ℝ)) ∧
    (∀ {m : ℕ} (T : SATDeciderTableau m 7),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 7) (Fin 7) ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intros m T
  · exact ⟨contentDrivenGauge_n2_posDef T, contentDrivenGauge_n2_ne_identity T⟩
  · exact ⟨contentDrivenGauge_n3_posDef T, contentDrivenGauge_n3_ne_identity T⟩
  · exact ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩
  · exact ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩
  · exact ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩
  · exact ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
