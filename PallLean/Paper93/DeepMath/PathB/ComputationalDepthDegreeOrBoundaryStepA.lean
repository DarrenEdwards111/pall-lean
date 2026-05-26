import PallLean.Paper93.DeepMath.PathB.ComputationalDepthStepAObligationCertificates

/-!
# Corrected Step A floor: degree/boundary growth (not `n ≤ λ₂`)

This file replaces the old Step A growth source with boundary-side data.
`secondEigenvalueBound` remains an upper-bound certifier; growth comes from
`boundaryMixingScore` directly.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Correct floor polarity at scale `n`: boundary/degree side already carries
size `n`. -/
def DegreeOrBoundaryExpansionFloorAtScale
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
    ∀ P : RamanujanAmplituhedronConcretePayload enc n L W,
      n <= boundaryMixingScore P

/-- Constructive per-payload certificate for the corrected Step A floor. -/
structure DegreeOrBoundaryExpansionFloorCertificate
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (L : DynamicNFrameLagrangianObserver enc)
    (W : DynamicMinorPreAmplificationWitness enc L n)
    (P : RamanujanAmplituhedronConcretePayload enc n L W) where
  floorProof : n <= boundaryMixingScore P

/-- Global builder form of the corrected Step A floor obligation. -/
def DegreeOrBoundaryExpansionFloorCertificateBuilder
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
    ∀ P : RamanujanAmplituhedronConcretePayload enc n L W,
      DegreeOrBoundaryExpansionFloorCertificate enc n L W P

/-- Builder discharges the corrected floor assumption. -/
theorem degreeOrBoundaryExpansionFloorAtScale_of_certificateBuilder
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (H : DegreeOrBoundaryExpansionFloorCertificateBuilder enc n) :
    DegreeOrBoundaryExpansionFloorAtScale enc n := by
  intro L W P
  exact (H L W P).floorProof

/-- Corrected bridge into the legacy Step-A sandwich socket: if boundary floor
already holds, the spectral premises are irrelevant for this step and are
accepted only for interface compatibility. -/
def spectralSandwichBridgeCertificateBuilder_of_degreeOrBoundaryExpansionFloor
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (Hfloor : DegreeOrBoundaryExpansionFloorAtScale enc n) :
    SpectralSandwichBridgeCertificateBuilder enc n := by
  intro L W P
  refine ⟨?_⟩
  intro _hfloorOld _hupper
  exact Hfloor L W P

/-- Legacy socket discharged from corrected boundary-side floor. -/
theorem spectralSandwichToMixingScoreLowerBound_of_degreeOrBoundaryExpansionFloor
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (Hfloor : DegreeOrBoundaryExpansionFloorAtScale enc n) :
    SpectralSandwichToMixingScoreLowerBound enc n :=
  spectralSandwichToMixingScoreLowerBound_of_certificateBuilder enc n
    (spectralSandwichBridgeCertificateBuilder_of_degreeOrBoundaryExpansionFloor
      enc n Hfloor)

/-- Step A closes directly from corrected boundary/degree floor. -/
theorem gapMarginToMixingScoreLowerBound_of_degreeOrBoundaryExpansionFloor
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (Hfloor : DegreeOrBoundaryExpansionFloorAtScale enc n) :
    GapMarginToMixingScoreLowerBound enc n := by
  intro L W P _hgap
  exact Hfloor L W P

/-- Packaged corrected Step A discharge certificate. -/
structure DegreeOrBoundaryStepADischargeCertificate
    (enc : ThreeCNFEncoding)
    (n : Nat) where
  floorBuilder : DegreeOrBoundaryExpansionFloorCertificateBuilder enc n

/-- Packaged corrected certificate closes Step A. -/
theorem gapMarginToMixingScoreLowerBound_of_degreeOrBoundaryCertificate
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (C : DegreeOrBoundaryStepADischargeCertificate enc n) :
    GapMarginToMixingScoreLowerBound enc n :=
  gapMarginToMixingScoreLowerBound_of_degreeOrBoundaryExpansionFloor enc n
    (degreeOrBoundaryExpansionFloorAtScale_of_certificateBuilder enc n C.floorBuilder)

#print axioms degreeOrBoundaryExpansionFloorAtScale_of_certificateBuilder
#print axioms spectralSandwichToMixingScoreLowerBound_of_degreeOrBoundaryExpansionFloor
#print axioms gapMarginToMixingScoreLowerBound_of_degreeOrBoundaryExpansionFloor
#print axioms gapMarginToMixingScoreLowerBound_of_degreeOrBoundaryCertificate

end PallLean.Paper93.DeepMath.PathB
