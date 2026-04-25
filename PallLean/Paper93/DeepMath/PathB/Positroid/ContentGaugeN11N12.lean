import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugePosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugeNotIdentityN2
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem contentDrivenGauge_n11_nontrivial {m : ℕ} (T : SATDeciderTableau m 11) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 11) (Fin 11) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num),
   contentDrivenGauge_ne_identity_general T (by norm_num)⟩

theorem contentDrivenGauge_n12_nontrivial {m : ℕ} (T : SATDeciderTableau m 12) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 12) (Fin 12) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num),
   contentDrivenGauge_ne_identity_general T (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
