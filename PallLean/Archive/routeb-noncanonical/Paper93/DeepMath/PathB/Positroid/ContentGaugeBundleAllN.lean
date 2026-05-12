import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugePosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugeNotIdentityN2
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- For any n ≥ 2 and any tableau, the content-driven gauge is PosDef and non-identity. -/
theorem contentDrivenGauge_universal_nontrivial {m n : ℕ} (T : SATDeciderTableau m n)
    (hn : 2 ≤ n) :
    (contentDrivenGauge T).PosDef ∧
    contentDrivenGauge T ≠ (1 : Matrix (Fin n) (Fin n) ℝ) := by
  refine ⟨?_, ?_⟩
  · exact contentDrivenGauge_posDef T (by omega : 1 ≤ n)
  · exact contentDrivenGauge_ne_identity_general T hn

/-- Existence form: for any n ≥ 2 and any tableau, ∃ non-identity PosDef gauge from content. -/
theorem exists_content_driven_nontrivial_universal {m n : ℕ} (T : SATDeciderTableau m n)
    (hn : 2 ≤ n) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      A.PosDef ∧
      A ≠ (1 : Matrix (Fin n) (Fin n) ℝ) ∧
      A = contentDrivenGauge T := by
  refine ⟨contentDrivenGauge T, ?_, ?_, rfl⟩
  · exact contentDrivenGauge_posDef T (by omega : 1 ≤ n)
  · exact contentDrivenGauge_ne_identity_general T hn

end PallLean.Paper93.DeepMath.PathB.Positroid
