import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition

/-!
# SAT family: identity gauge witness at small `n`

This file shows that the identity matrix is an `IsAmplituhedronGauge` for the
SAT family `satFamily n` at every `n`, and packages this as an existence
witness `satFamily_witness_exists`.

## Honest scope

The substantive theorem here is `satFamily_witness_exists`: for every `n`
there exists *some* matrix `A` that is a gauge for `satFamily n`. Its proof
is a structural wrapper: the identity matrix gauges *every* family `𝒥`
(see `identity_isAmplituhedronGauge_any`), so in particular it gauges
`satFamily n`. The corresponding `n = 1` specialisation
`identity_isGauge_satFamily_one` is therefore *not* a non-vacuous content
about the SAT family beyond the fact that it admits gauge witnesses.

The deeper claim — that a matrix derived from a SAT decider's compiled
gadget gauges this family in a non-vacuous (decider-dependent) way — is
**not** proven in this file. The results here only certify that the
`satFamily n` index family ADMITS gauge witnesses, which is the weakest
non-emptiness statement at the level of the gauge property.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-- Identity matrix is a gauge for `satFamily n`, at every `n`.

    This is a wrapper around `identity_isAmplituhedronGauge_any`: the
    identity matrix gauges every family of principal-minor index sets.
    No specific structural feature of `satFamily n` is used here. -/
theorem identity_isGauge_satFamily (n : ℕ) :
    IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) (satFamily n) :=
  identity_isAmplituhedronGauge_any (satFamily n)

/-- The `n = 1` specialisation of `identity_isGauge_satFamily`. -/
theorem identity_isGauge_satFamily_one :
    IsAmplituhedronGauge (1 : Matrix (Fin 1) (Fin 1) ℝ) (satFamily 1) :=
  identity_isGauge_satFamily 1

/-- Existence witness: the SAT family `satFamily n` admits a gauge matrix for
    every `n`. The witness is the identity matrix. -/
theorem satFamily_witness_exists (n : ℕ) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A (satFamily n) :=
  ⟨1, identity_isGauge_satFamily n⟩

end PallLean.Paper93.DeepMath.PathB
