import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugePosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugeNotIdentityN2
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem contentDrivenGauge_n13_nontrivial {m : ℕ} (T : SATDeciderTableau m 13) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 13) (Fin 13) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num),
   contentDrivenGauge_ne_identity_general T (by norm_num)⟩

theorem contentDrivenGauge_n14_nontrivial {m : ℕ} (T : SATDeciderTableau m 14) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 14) (Fin 14) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num),
   contentDrivenGauge_ne_identity_general T (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
