import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugePosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugeNotIdentityN2
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Universal existence of content-driven gauges for any `n ≥ 2`

This kernel-only file packages the existence of a non-trivial
content-driven gauge for **every** `SATDeciderTableau m n` with
`n ≥ 2`, by combining:

- `contentDrivenGauge_posDef` (positive definiteness for any `1 ≤ n`),
- `contentDrivenGauge_ne_identity_general` (non-identity for `2 ≤ n`),

into a single `∃` statement.  We additionally record a uniformly
non-trivial bundling for the small-dimension cases `n = 2, 3` using the
specialised lemmas `contentDrivenGauge_n{2,3}_posDef` and
`contentDrivenGauge_n{2,3}_ne_identity`.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem contentDrivenGauge_exists_for_all_tableaus :
    ∀ {m n : ℕ} (T : SATDeciderTableau m n) (_ : 2 ≤ n),
      ∃ A : Matrix (Fin n) (Fin n) ℝ,
        A.PosDef ∧ A ≠ (1 : Matrix (Fin n) (Fin n) ℝ) := by
  intros m n T hn
  refine ⟨contentDrivenGauge T, ?_, ?_⟩
  · exact contentDrivenGauge_posDef T (by omega : 1 ≤ n)
  · exact contentDrivenGauge_ne_identity_general T hn

theorem contentDrivenGauge_uniformly_nontrivial :
    ∀ {m : ℕ} (T₁ : SATDeciderTableau m 2) (T₂ : SATDeciderTableau m 3),
      ((contentDrivenGauge T₁).PosDef ∧ contentDrivenGauge T₁ ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      ((contentDrivenGauge T₂).PosDef ∧ contentDrivenGauge T₂ ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
  intros m T₁ T₂
  refine ⟨?_, ?_⟩
  · exact ⟨contentDrivenGauge_n2_posDef T₁, contentDrivenGauge_n2_ne_identity T₁⟩
  · exact ⟨contentDrivenGauge_n3_posDef T₂, contentDrivenGauge_n3_ne_identity T₂⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
