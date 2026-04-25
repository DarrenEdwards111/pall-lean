import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugePosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugeNotIdentityN2
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem contentDrivenGauge_n9_nontrivial {m : ℕ} (T : SATDeciderTableau m 9) :
    (contentDrivenGauge T).PosDef ∧
    contentDrivenGauge T ≠ (1 : Matrix (Fin 9) (Fin 9) ℝ) := by
  refine ⟨?_, ?_⟩
  · exact contentDrivenGauge_posDef T (by norm_num : 1 ≤ 9)
  · exact contentDrivenGauge_ne_identity_general T (by norm_num : 2 ≤ 9)

theorem contentDrivenGauge_n10_nontrivial {m : ℕ} (T : SATDeciderTableau m 10) :
    (contentDrivenGauge T).PosDef ∧
    contentDrivenGauge T ≠ (1 : Matrix (Fin 10) (Fin 10) ℝ) := by
  refine ⟨?_, ?_⟩
  · exact contentDrivenGauge_posDef T (by norm_num : 1 ≤ 10)
  · exact contentDrivenGauge_ne_identity_general T (by norm_num : 2 ≤ 10)

end PallLean.Paper93.DeepMath.PathB.Positroid
