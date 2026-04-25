import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugePosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugeNotIdentityN2
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem contentDrivenGauge_n21_nontrivial {m : ℕ} (T : SATDeciderTableau m 21) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 21) (Fin 21) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

theorem contentDrivenGauge_n22_nontrivial {m : ℕ} (T : SATDeciderTableau m 22) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 22) (Fin 22) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

theorem contentDrivenGauge_n23_nontrivial {m : ℕ} (T : SATDeciderTableau m 23) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 23) (Fin 23) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

theorem contentDrivenGauge_n24_nontrivial {m : ℕ} (T : SATDeciderTableau m 24) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 24) (Fin 24) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

theorem contentDrivenGauge_n26_nontrivial {m : ℕ} (T : SATDeciderTableau m 26) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 26) (Fin 26) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

theorem contentDrivenGauge_n27_nontrivial {m : ℕ} (T : SATDeciderTableau m 27) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 27) (Fin 27) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

theorem contentDrivenGauge_n28_nontrivial {m : ℕ} (T : SATDeciderTableau m 28) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 28) (Fin 28) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

theorem contentDrivenGauge_n29_nontrivial {m : ℕ} (T : SATDeciderTableau m 29) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 29) (Fin 29) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

theorem contentDrivenGauge_n30_nontrivial {m : ℕ} (T : SATDeciderTableau m 30) :
    (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 30) (Fin 30) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by norm_num), contentDrivenGauge_ne_identity_general T (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
