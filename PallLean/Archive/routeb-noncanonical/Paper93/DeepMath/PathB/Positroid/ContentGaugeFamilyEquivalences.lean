import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- The extracted family of any tableau coincides with satFamily n. -/
theorem extractedFamily_equals_satFamily (m n : ℕ) (T : SATDeciderTableau m n) :
    T.extractedFamily = satFamily n := rfl

/-- The extracted family contains both extremal index sets at any n. -/
theorem extractedFamily_extremals (m n : ℕ) (T : SATDeciderTableau m n) :
    ∅ ∈ T.extractedFamily ∧ (Finset.univ : Finset (Fin n)) ∈ T.extractedFamily :=
  ⟨T.extractedFamily_mem_empty, T.extractedFamily_mem_univ⟩

/-- All zero-tableaus at the same dimension have the same extracted family. -/
theorem zero_tableaus_same_extractedFamily (m₁ m₂ n : ℕ) :
    (SATDeciderTableau.zero m₁ n).extractedFamily = (SATDeciderTableau.zero m₂ n).extractedFamily :=
  rfl

end PallLean.Paper93.DeepMath.PathB.Positroid
