import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCheegerCertificateRoute

/-!
# Gap-to-boundary core decomposition

Further isolates the load-bearing theorem `GapMarginToBoundaryLowerBound` into
an explicit two-step route.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Intermediate boundary-mixing score attached to a payload. -/
def boundaryMixingScore
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : DynamicNFrameLagrangianObserver enc}
    {W : DynamicMinorPreAmplificationWitness enc L n}
    (P : RamanujanAmplituhedronConcretePayload enc n L W) : Nat :=
  P.expanderGraph.degree

/-- Step A: nonnegative spectral gap margin implies a lower bound on the
intermediate boundary-mixing score. -/
def GapMarginToMixingScoreLowerBound
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
    ∀ P : RamanujanAmplituhedronConcretePayload enc n L W,
      0 <= spectralGapMargin P ->
      n <= boundaryMixingScore P

/-- Step B: mixing score lower bound transfers to boundary operator lower bound.
-/
def MixingScoreToBoundaryOperatorLowerBound
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
    ∀ P : RamanujanAmplituhedronConcretePayload enc n L W,
      n <= boundaryMixingScore P ->
      n <= boundaryOperatorValue P

/-- Compose Step A and B to discharge `GapMarginToBoundaryLowerBound`. -/
theorem gapMarginToBoundaryLowerBound_of_twoStep
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (Hmix : GapMarginToMixingScoreLowerBound enc n)
    (Htransfer : MixingScoreToBoundaryOperatorLowerBound enc n) :
    GapMarginToBoundaryLowerBound enc n := by
  intro L W P hgap
  have hscore : n <= boundaryMixingScore P := Hmix L W P hgap
  exact Htransfer L W P hscore

#print axioms gapMarginToBoundaryLowerBound_of_twoStep

end PallLean.Paper93.DeepMath.PathB
