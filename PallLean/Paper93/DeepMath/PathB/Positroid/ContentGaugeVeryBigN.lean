import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugePosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugeNotIdentityN2
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem contentDrivenGauge_n25_nontrivial {m : ℕ} (T : SATDeciderTableau m 25) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 25) (Fin 25) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

theorem contentDrivenGauge_n50_nontrivial {m : ℕ} (T : SATDeciderTableau m 50) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 50) (Fin 50) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

theorem contentDrivenGauge_n100_nontrivial {m : ℕ} (T : SATDeciderTableau m 100) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 100) (Fin 100) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
