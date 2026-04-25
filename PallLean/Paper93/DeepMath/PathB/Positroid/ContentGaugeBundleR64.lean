import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugePosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugeNotIdentityN2
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem content_driven_gauge_bundle_2_to_10 :
    (∀ {m : ℕ} (T : SATDeciderTableau m 2),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∀ {m : ℕ} (T : SATDeciderTableau m 3),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ)) ∧
    (∀ {m : ℕ} (T : SATDeciderTableau m 4),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 4) (Fin 4) ℝ)) ∧
    (∀ {m : ℕ} (T : SATDeciderTableau m 5),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 5) (Fin 5) ℝ)) ∧
    (∀ {m : ℕ} (T : SATDeciderTableau m 6),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 6) (Fin 6) ℝ)) ∧
    (∀ {m : ℕ} (T : SATDeciderTableau m 7),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 7) (Fin 7) ℝ)) ∧
    (∀ {m : ℕ} (T : SATDeciderTableau m 8),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 8) (Fin 8) ℝ)) ∧
    (∀ {m : ℕ} (T : SATDeciderTableau m 9),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 9) (Fin 9) ℝ)) ∧
    (∀ {m : ℕ} (T : SATDeciderTableau m 10),
      (contentDrivenGauge T).PosDef ∧ contentDrivenGauge T ≠ (1 : Matrix (Fin 10) (Fin 10) ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros _ T
    exact ⟨contentDrivenGauge_posDef T (by norm_num),
           contentDrivenGauge_ne_identity_general T (by norm_num)⟩
  · intros _ T
    exact ⟨contentDrivenGauge_posDef T (by norm_num),
           contentDrivenGauge_ne_identity_general T (by norm_num)⟩
  · intros _ T
    exact ⟨contentDrivenGauge_posDef T (by norm_num),
           contentDrivenGauge_ne_identity_general T (by norm_num)⟩
  · intros _ T
    exact ⟨contentDrivenGauge_posDef T (by norm_num),
           contentDrivenGauge_ne_identity_general T (by norm_num)⟩
  · intros _ T
    exact ⟨contentDrivenGauge_posDef T (by norm_num),
           contentDrivenGauge_ne_identity_general T (by norm_num)⟩
  · intros _ T
    exact ⟨contentDrivenGauge_posDef T (by norm_num),
           contentDrivenGauge_ne_identity_general T (by norm_num)⟩
  · intros _ T
    exact ⟨contentDrivenGauge_posDef T (by norm_num),
           contentDrivenGauge_ne_identity_general T (by norm_num)⟩
  · intros _ T
    exact ⟨contentDrivenGauge_posDef T (by norm_num),
           contentDrivenGauge_ne_identity_general T (by norm_num)⟩
  · intros _ T
    exact ⟨contentDrivenGauge_posDef T (by norm_num),
           contentDrivenGauge_ne_identity_general T (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
