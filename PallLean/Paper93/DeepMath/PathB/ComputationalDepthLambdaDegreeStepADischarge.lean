import PallLean.Paper93.DeepMath.PathB.ComputationalDepthStepAObligationCertificates

/-!
# λ₂ ≤ degree discharge for Step A

This file anchors the constructive Step A certificate interface to the concrete
spectral model assumption Darren selected:

* the payload graph satisfies `λ₂ ≤ degree`, expressed for the existing rational
  second-eigenvalue bound;
* the still-independent scale floor `n ≤ λ₂` is supplied by the existing floor
  certificate builder.

Under those two concrete model inputs, the spectral-sandwich obligation is no
longer a socket: the floor and `λ₂ ≤ degree` mechanically give
`n ≤ degree = boundaryMixingScore P`, and hence Step A follows through the
already-proved certificate chain.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Payload-level spectral model assumption selected for this discharge:
the second-eigenvalue bound is at most the graph degree. -/
def LambdaTwoLeDegreeModel
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
    ∀ P : RamanujanAmplituhedronConcretePayload enc n L W,
      P.spectral.secondEigenvalueBound <=
        Rat.ofInt (Int.ofNat P.expanderGraph.degree)

/-- The selected model assumption converts the floor `n ≤ λ₂` directly into the
mixing-score lower bound, since `boundaryMixingScore P` is the graph degree. -/
theorem mixingScoreLowerBound_of_floor_and_lambdaTwoLeDegree
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : DynamicNFrameLagrangianObserver enc}
    {W : DynamicMinorPreAmplificationWitness enc L n}
    (P : RamanujanAmplituhedronConcretePayload enc n L W)
    (hfloor : Rat.ofInt (Int.ofNat n) <= P.spectral.secondEigenvalueBound)
    (hlambdaDegree :
      P.spectral.secondEigenvalueBound <=
        Rat.ofInt (Int.ofNat P.expanderGraph.degree)) :
    n <= boundaryMixingScore P := by
  have hrat : Rat.ofInt (Int.ofNat n) <=
      Rat.ofInt (Int.ofNat P.expanderGraph.degree) :=
    le_trans hfloor hlambdaDegree
  have hnat : n <= P.expanderGraph.degree := by
    have hcast : (n : Rat) <= (P.expanderGraph.degree : Rat) := by
      simpa using hrat
    exact_mod_cast hcast
  simpa [boundaryMixingScore] using hnat

/-- The λ₂≤degree model discharges the spectral-sandwich bridge builder.  The
Ramanujan upper-bound premise is accepted for compatibility with the earlier
interface but is no longer load-bearing for this degree route. -/
def spectralSandwichBridgeCertificateBuilder_of_lambdaTwoLeDegree
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (HlambdaDegree : LambdaTwoLeDegreeModel enc n) :
    SpectralSandwichBridgeCertificateBuilder enc n := by
  intro L W P
  refine ⟨?_⟩
  intro hfloor _hRamanujanUpper
  exact mixingScoreLowerBound_of_floor_and_lambdaTwoLeDegree P hfloor
    (HlambdaDegree L W P)

/-- Same discharge phrased at the original Step A sandwich-obligation level. -/
theorem spectralSandwichToMixingScoreLowerBound_of_lambdaTwoLeDegree
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (HlambdaDegree : LambdaTwoLeDegreeModel enc n) :
    SpectralSandwichToMixingScoreLowerBound enc n :=
  spectralSandwichToMixingScoreLowerBound_of_certificateBuilder enc n
    (spectralSandwichBridgeCertificateBuilder_of_lambdaTwoLeDegree enc n
      HlambdaDegree)

/-- Full Step A discharge chain under the selected λ₂≤degree model plus the
independent concrete λ₂ floor certificate builder. -/
theorem gapMarginToMixingScoreLowerBound_of_floorBuilder_and_lambdaTwoLeDegree
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (Hfloor : SpectralFloorCertificateBuilder enc n)
    (HlambdaDegree : LambdaTwoLeDegreeModel enc n) :
    GapMarginToMixingScoreLowerBound enc n :=
  gapMarginToMixingScoreLowerBound_of_spectralSandwich enc n
    (spectralFloorAtScale_of_certificateBuilder enc n Hfloor)
    (spectralSandwichToMixingScoreLowerBound_of_lambdaTwoLeDegree enc n
      HlambdaDegree)

/-- Certificate-packaged version: from a floor certificate builder and the
λ₂≤degree model, build both constructive certificates needed by Step A. -/
structure LambdaDegreeStepADischargeCertificate
    (enc : ThreeCNFEncoding)
    (n : Nat) where
  floorBuilder : SpectralFloorCertificateBuilder enc n
  lambdaTwo_le_degree : LambdaTwoLeDegreeModel enc n

/-- A packaged λ₂≤degree Step A discharge certificate closes the Step A mixing
bound. -/
theorem gapMarginToMixingScoreLowerBound_of_lambdaDegreeCertificate
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (C : LambdaDegreeStepADischargeCertificate enc n) :
    GapMarginToMixingScoreLowerBound enc n :=
  gapMarginToMixingScoreLowerBound_of_floorBuilder_and_lambdaTwoLeDegree enc n
    C.floorBuilder C.lambdaTwo_le_degree

#print axioms mixingScoreLowerBound_of_floor_and_lambdaTwoLeDegree
#print axioms spectralSandwichToMixingScoreLowerBound_of_lambdaTwoLeDegree
#print axioms gapMarginToMixingScoreLowerBound_of_floorBuilder_and_lambdaTwoLeDegree
#print axioms gapMarginToMixingScoreLowerBound_of_lambdaDegreeCertificate

end PallLean.Paper93.DeepMath.PathB
