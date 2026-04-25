import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugePosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugeNotIdentityN2
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem contentDrivenGauge_n15_nontrivial {m : ℕ} (T : SATDeciderTableau m 15) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 15) (Fin 15) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

theorem contentDrivenGauge_n16_nontrivial {m : ℕ} (T : SATDeciderTableau m 16) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 16) (Fin 16) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

theorem contentDrivenGauge_n17_nontrivial {m : ℕ} (T : SATDeciderTableau m 17) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 17) (Fin 17) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

theorem contentDrivenGauge_n18_nontrivial {m : ℕ} (T : SATDeciderTableau m 18) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 18) (Fin 18) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

theorem contentDrivenGauge_n19_nontrivial {m : ℕ} (T : SATDeciderTableau m 19) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 19) (Fin 19) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

theorem contentDrivenGauge_n20_nontrivial {m : ℕ} (T : SATDeciderTableau m 20) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 20) (Fin 20) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
