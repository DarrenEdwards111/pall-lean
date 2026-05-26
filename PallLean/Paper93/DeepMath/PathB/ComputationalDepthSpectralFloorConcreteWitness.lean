import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLambdaDegreeStepADischarge

/-!
# Concrete spectral-floor witness for Step A

This file turns the remaining `n ≤ λ₂` obligation into an explicit constructive
witness form: each payload carries a natural slack `k` with
`λ₂ = n + k` (as the existing rational bound). From that data, the floor
certificate is automatic.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Concrete payload witness for the spectral floor at scale `n`.
The second-eigenvalue bound is exhibited as `n + slack`. -/
structure SpectralFloorConcreteWitness
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (L : DynamicNFrameLagrangianObserver enc)
    (W : DynamicMinorPreAmplificationWitness enc L n)
    (P : RamanujanAmplituhedronConcretePayload enc n L W) where
  slack : Nat
  lambda_two_eq :
    P.spectral.secondEigenvalueBound =
      Rat.ofInt (Int.ofNat (n + slack))

/-- Builder form: provide a concrete floor witness for every payload. -/
def SpectralFloorConcreteWitnessBuilder
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
    ∀ P : RamanujanAmplituhedronConcretePayload enc n L W,
      Nonempty (SpectralFloorConcreteWitness enc n L W P)

/-- A concrete floor witness discharges the per-payload floor certificate. -/
theorem spectralFloorCertificate_of_concreteWitness
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : DynamicNFrameLagrangianObserver enc}
    {W : DynamicMinorPreAmplificationWitness enc L n}
    {P : RamanujanAmplituhedronConcretePayload enc n L W}
    (hW : SpectralFloorConcreteWitness enc n L W P) :
    SpectralFloorCertificate enc n L W P := by
  refine ⟨?_⟩
  have hnat : n <= n + hW.slack := Nat.le_add_right n hW.slack
  have hrat' : (n : Rat) <= (n + hW.slack : Rat) := by
    exact_mod_cast hnat
  have hrat : Rat.ofInt (Int.ofNat n) <= Rat.ofInt (Int.ofNat (n + hW.slack)) := by
    simpa using hrat'
  simpa [hW.lambda_two_eq] using hrat

/-- A concrete witness builder discharges the global Step A floor builder. -/
theorem spectralFloorCertificateBuilder_of_concreteWitnessBuilder
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (H : SpectralFloorConcreteWitnessBuilder enc n) :
    SpectralFloorCertificateBuilder enc n := by
  intro L W P
  rcases H L W P with ⟨hW⟩
  exact spectralFloorCertificate_of_concreteWitness hW

/-- Full Step A discharge from (i) concrete floor witnesses and
(ii) the selected λ₂≤degree model. -/
theorem gapMarginToMixingScoreLowerBound_of_concreteFloorWitness_and_lambdaTwoLeDegree
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (Hfloor : SpectralFloorConcreteWitnessBuilder enc n)
    (HlambdaDegree : LambdaTwoLeDegreeModel enc n) :
    GapMarginToMixingScoreLowerBound enc n :=
  gapMarginToMixingScoreLowerBound_of_floorBuilder_and_lambdaTwoLeDegree enc n
    (spectralFloorCertificateBuilder_of_concreteWitnessBuilder enc n Hfloor)
    HlambdaDegree

#print axioms spectralFloorCertificate_of_concreteWitness
#print axioms spectralFloorCertificateBuilder_of_concreteWitnessBuilder
#print axioms gapMarginToMixingScoreLowerBound_of_concreteFloorWitness_and_lambdaTwoLeDegree

end PallLean.Paper93.DeepMath.PathB
