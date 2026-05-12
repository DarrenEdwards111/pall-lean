import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef

/-!
# Tableau-to-Gauge-Family Bridge

This file provides a structured bridge from a SAT-decider tableau (the toy
Cook--Levin compiled-gadget data of `SATDeciderTableauToy.lean`) to the
amplituhedron gauge property of `GaugePropertyDef.lean`. The construction
exploits the fact that the identity matrix gauges *any* finite family of
index sets (`identity_isAmplituhedronGauge_any`), and so in particular it
gauges the family extracted from any SAT-decider tableau.

The main theorem `tableau_to_gauge_bridge` packages this as: every
SAT-decider tableau admits an amplituhedron gauge witness on its
extracted family.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB

/-- For any SAT decider tableau, the identity matrix gauges its extracted family. -/
theorem identity_gauges_extractedFamily {m n : ℕ} (T : SATDeciderTableau m n) :
    IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) T.extractedFamily :=
  identity_isAmplituhedronGauge_any T.extractedFamily

/-- For any SAT decider tableau, there exists a gauge witness for its extracted family. -/
theorem exists_gauge_for_tableau {m n : ℕ} (T : SATDeciderTableau m n) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A T.extractedFamily :=
  ⟨1, identity_gauges_extractedFamily T⟩

/-- The all-ones tableau extracts a gauge family that admits identity as gauge. -/
theorem identity_gauges_allOnes_family (m n : ℕ) :
    IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ)
      (SATDeciderTableau.allOnes m n).extractedFamily :=
  identity_gauges_extractedFamily (SATDeciderTableau.allOnes m n)

/-- The zero tableau extracts a gauge family that admits identity as gauge. -/
theorem identity_gauges_zero_family (m n : ℕ) :
    IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ)
      (SATDeciderTableau.zero m n).extractedFamily :=
  identity_gauges_extractedFamily (SATDeciderTableau.zero m n)

/-- **Bridge theorem**: any SAT decider tableau admits an amplituhedron gauge witness. -/
theorem tableau_to_gauge_bridge :
    ∀ (m n : ℕ) (T : SATDeciderTableau m n),
      ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A T.extractedFamily :=
  fun m n T => exists_gauge_for_tableau T

end PallLean.Paper93.DeepMath.PathB.Positroid
