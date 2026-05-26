import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGapToBoundaryCore

/-!
# Step A decomposition: gap margin -> mixing score

Makes the Step A frontier explicit by splitting it into:
1) extracting the Ramanujan spectral upper bound from a nonnegative gap margin,
2) a load-bearing spectral-to-degree lower-bound socket.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- From nonnegative margin, recover the Ramanujan spectral upper bound. -/
theorem spectralUpper_of_gapMarginNonneg
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : DynamicNFrameLagrangianObserver enc}
    {W : DynamicMinorPreAmplificationWitness enc L n}
    (P : RamanujanAmplituhedronConcretePayload enc n L W)
    (hgap : 0 <= spectralGapMargin P) :
    P.spectral.secondEigenvalueBound <=
      (2 : Rat) * Rat.ofInt (Int.ofNat (Nat.sqrt (P.expanderGraph.degree - 1))) := by
  dsimp [spectralGapMargin] at hgap
  exact sub_nonneg.mp hgap

/-- Load-bearing socket: a spectral floor together with the Ramanujan upper
bound implies degree (mixing score) lower bound. -/
def SpectralSandwichToMixingScoreLowerBound
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
    ∀ P : RamanujanAmplituhedronConcretePayload enc n L W,
      Rat.ofInt (Int.ofNat n) <= P.spectral.secondEigenvalueBound ->
      P.spectral.secondEigenvalueBound <=
        (2 : Rat) * Rat.ofInt (Int.ofNat (Nat.sqrt (P.expanderGraph.degree - 1))) ->
      n <= boundaryMixingScore P

/-- Explicit floor assumption for λ₂ at size `n`. -/
def SpectralFloorAtScale
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
    ∀ P : RamanujanAmplituhedronConcretePayload enc n L W,
      Rat.ofInt (Int.ofNat n) <= P.spectral.secondEigenvalueBound

/-- Step A follows from (i) a spectral floor and (ii) the load-bearing
spectral sandwich to degree bridge. -/
theorem gapMarginToMixingScoreLowerBound_of_spectralSandwich
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (Hfloor : SpectralFloorAtScale enc n)
    (Hsandwich : SpectralSandwichToMixingScoreLowerBound enc n) :
    GapMarginToMixingScoreLowerBound enc n := by
  intro L W P hgap
  have hu :
      P.spectral.secondEigenvalueBound <=
        (2 : Rat) * Rat.ofInt (Int.ofNat (Nat.sqrt (P.expanderGraph.degree - 1))) :=
    spectralUpper_of_gapMarginNonneg P hgap
  exact Hsandwich L W P (Hfloor L W P) hu

#print axioms spectralUpper_of_gapMarginNonneg
#print axioms gapMarginToMixingScoreLowerBound_of_spectralSandwich

end PallLean.Paper93.DeepMath.PathB
