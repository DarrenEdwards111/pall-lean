import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGapToMixingStepA

/-!
# Step A obligation certificates

Constructive certificate forms for the two remaining Step A obligations.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Concrete per-payload certificate for the λ₂ floor at scale `n`. -/
structure SpectralFloorCertificate
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (L : DynamicNFrameLagrangianObserver enc)
    (W : DynamicMinorPreAmplificationWitness enc L n)
    (P : RamanujanAmplituhedronConcretePayload enc n L W) where
  floorProof : Rat.ofInt (Int.ofNat n) <= P.spectral.secondEigenvalueBound

/-- Global builder form of the λ₂ floor obligation. -/
def SpectralFloorCertificateBuilder
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
    ∀ P : RamanujanAmplituhedronConcretePayload enc n L W,
      SpectralFloorCertificate enc n L W P

/-- Certificate-builder discharges `SpectralFloorAtScale`. -/
theorem spectralFloorAtScale_of_certificateBuilder
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (H : SpectralFloorCertificateBuilder enc n) :
    SpectralFloorAtScale enc n := by
  intro L W P
  exact (H L W P).floorProof

/-- Concrete per-payload certificate for the spectral-sandwich => degree step. -/
structure SpectralSandwichBridgeCertificate
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (L : DynamicNFrameLagrangianObserver enc)
    (W : DynamicMinorPreAmplificationWitness enc L n)
    (P : RamanujanAmplituhedronConcretePayload enc n L W) where
  bridgeProof :
    Rat.ofInt (Int.ofNat n) <= P.spectral.secondEigenvalueBound ->
    P.spectral.secondEigenvalueBound <=
      (2 : Rat) * Rat.ofInt (Int.ofNat (Nat.sqrt (P.expanderGraph.degree - 1))) ->
    n <= boundaryMixingScore P

/-- Global builder form of the sandwich bridge obligation. -/
def SpectralSandwichBridgeCertificateBuilder
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
    ∀ P : RamanujanAmplituhedronConcretePayload enc n L W,
      SpectralSandwichBridgeCertificate enc n L W P

/-- Certificate-builder discharges `SpectralSandwichToMixingScoreLowerBound`. -/
theorem spectralSandwichToMixingScoreLowerBound_of_certificateBuilder
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (H : SpectralSandwichBridgeCertificateBuilder enc n) :
    SpectralSandwichToMixingScoreLowerBound enc n := by
  intro L W P hfloor hup
  exact (H L W P).bridgeProof hfloor hup

#print axioms spectralFloorAtScale_of_certificateBuilder
#print axioms spectralSandwichToMixingScoreLowerBound_of_certificateBuilder

end PallLean.Paper93.DeepMath.PathB
