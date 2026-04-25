import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugePosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugeNotIdentityN2
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem content_driven_gauge_universal_2_to_14 (n : ℕ) (hn : 2 ≤ n) (hn14 : n ≤ 14)
    {m : ℕ} (T : SATDeciderTableau m n) :
    (contentDrivenGauge T).PosDef ∧
    contentDrivenGauge T ≠ (1 : Matrix (Fin n) (Fin n) ℝ) :=
  ⟨contentDrivenGauge_posDef T (by omega),
   contentDrivenGauge_ne_identity_general T hn⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
