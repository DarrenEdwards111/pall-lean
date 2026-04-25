import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.PathB.SATDeciderHypothesis
import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily

namespace PallLean.Paper93.DeepMath.PathB

/-- "SAT-tied gauge" property: a gauge A whose structure encodes a specific SAT decider.
    This is a placeholder definition — the actual paper §28.3 condition relates A to the
    SAT decider's compiled-gadget tableau. -/
def IsSATTiedGauge (decider : SATDecider) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (𝒥 : Finset (Finset (Fin n))) : Prop :=
  IsAmplituhedronGauge A 𝒥 ∧ (∃ _ : SATDecider, decider = decider)

/-- Identity matrix is trivially SAT-tied (the SAT-tying clause is vacuous).
    NOTE: This is the WEAK form of "SAT-tied". The paper's stronger requirement is that
    the gauge's matrix structure encodes the decider's tableau. -/
theorem identity_isSATTiedGauge (decider : SATDecider) {n : ℕ}
    (𝒥 : Finset (Finset (Fin n))) :
    IsSATTiedGauge decider (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥 :=
  ⟨PallLean.Paper93.DeepMath.PathB.identity_isAmplituhedronGauge_any 𝒥, ⟨decider, rfl⟩⟩

end PallLean.Paper93.DeepMath.PathB
