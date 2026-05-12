import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugePosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugeNotIdentityN2
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem contentDrivenGauge_n8_nontrivial {m : ℕ} (T : SATDeciderTableau m 8) :
    (contentDrivenGauge T).PosDef ∧
    contentDrivenGauge T ≠ (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  refine ⟨?_, ?_⟩
  · exact contentDrivenGauge_posDef T (by norm_num : 1 ≤ 8)
  · exact contentDrivenGauge_ne_identity_general T (by norm_num : 2 ≤ 8)

theorem exists_content_driven_nontrivial_n8 :
    ∀ (m : ℕ) (T : SATDeciderTableau m 8),
      ∃ A : Matrix (Fin 8) (Fin 8) ℝ,
        A.PosDef ∧ A ≠ (1 : Matrix (Fin 8) (Fin 8) ℝ) ∧ A = contentDrivenGauge T := by
  intros m T
  refine ⟨contentDrivenGauge T, ?_, ?_, rfl⟩
  · exact contentDrivenGauge_posDef T (by norm_num : 1 ≤ 8)
  · exact contentDrivenGauge_ne_identity_general T (by norm_num : 2 ≤ 8)

end PallLean.Paper93.DeepMath.PathB.Positroid
