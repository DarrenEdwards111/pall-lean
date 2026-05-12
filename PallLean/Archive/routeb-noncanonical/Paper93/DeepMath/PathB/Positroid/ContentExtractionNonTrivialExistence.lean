import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugePosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugeNotIdentityN2
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Content-driven non-trivial extraction existence

This file packages the *existence* of a content-driven non-trivial
extraction for any `SATDeciderTableau m 2`: starting from the tableau's
own content (via `contentDrivenGauge`), one obtains a `Matrix.PosDef`
matrix on `Fin 2` that is genuinely **not** the identity.

The proof is a direct combination of:
- `contentDrivenGauge_n2_posDef` (positive definiteness of the
  content-driven gauge at `n = 2`), and
- `contentDrivenGauge_n2_ne_identity` (non-identity of the content-driven
  gauge at `n = 2`).

We additionally record the distinguishability of the zero vs all-ones
tableaus at `m = n = 2` at the *coupling* level
(`contentDrivenAlpha`), and an existence form witnessing two tableaus
that produce different content-driven gauges. Finally, we restate the
non-identity property for arbitrary `n ≥ 2`.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Content-driven non-trivial extraction existence.**

    For ANY n=2 SAT decider tableau, there exists a NON-IDENTITY PosDef matrix
    derived from the tableau's content (via `contentDrivenGauge`). -/
theorem exists_content_driven_nontrivial_n2 :
    ∀ (m : ℕ) (T : SATDeciderTableau m 2),
      ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
        A.PosDef ∧
        A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
        A = contentDrivenGauge T := by
  intros m T
  refine ⟨contentDrivenGauge T, ?_, ?_, rfl⟩
  · exact contentDrivenGauge_n2_posDef T
  · exact contentDrivenGauge_n2_ne_identity T

/-- For zero vs all-ones tableaus at m=n=2, the content-driven extraction
    distinguishes them at the coupling level. -/
theorem content_driven_distinguishes_zero_allOnes_n2 :
    contentDrivenAlpha (SATDeciderTableau.zero 2 2) ≠
    contentDrivenAlpha (SATDeciderTableau.allOnes 2 2) := by
  apply contentDrivenAlpha_distinguishes
  norm_num

/-- Existence form: there are tableaus producing different content-driven gauges. -/
theorem exists_distinguishable_content_driven_gauges :
    ∃ (T₁ T₂ : SATDeciderTableau 2 2),
      contentDrivenAlpha T₁ ≠ contentDrivenAlpha T₂ :=
  ⟨SATDeciderTableau.zero 2 2, SATDeciderTableau.allOnes 2 2,
   content_driven_distinguishes_zero_allOnes_n2⟩

/-- For any n ≥ 2 and any tableau, content-driven gauge is non-identity. -/
theorem content_driven_nontrivial_general {m n : ℕ} (T : SATDeciderTableau m n)
    (hn : 2 ≤ n) :
    contentDrivenGauge T ≠ (1 : Matrix (Fin n) (Fin n) ℝ) :=
  contentDrivenGauge_ne_identity_general T hn

end PallLean.Paper93.DeepMath.PathB.Positroid
