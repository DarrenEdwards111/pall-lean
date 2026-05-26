import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCheegerMixingTargets

/-!
# Cheeger certificate route

Builds a concrete route to `CheegerMixingCertificateBuilder` that explicitly
uses the spectral inequality via a nonnegative gap margin.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Ramanujan gap margin `2√(d-1) - λ₂`. -/
def spectralGapMargin
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : DynamicNFrameLagrangianObserver enc}
    {W : DynamicMinorPreAmplificationWitness enc L n}
    (P : RamanujanAmplituhedronConcretePayload enc n L W) : Rat :=
  (2 : Rat) * Rat.ofInt (Int.ofNat (Nat.sqrt (P.expanderGraph.degree - 1))) -
    P.spectral.secondEigenvalueBound

/-- Spectral premise implies nonnegative gap margin. -/
theorem spectralGapMargin_nonneg
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : DynamicNFrameLagrangianObserver enc}
    {W : DynamicMinorPreAmplificationWitness enc L n}
    (P : RamanujanAmplituhedronConcretePayload enc n L W)
    (hspectral :
      P.spectral.secondEigenvalueBound <=
        (2 : Rat) * Rat.ofInt (Int.ofNat (Nat.sqrt (P.expanderGraph.degree - 1)))) :
    0 <= spectralGapMargin P := by
  dsimp [spectralGapMargin]
  exact sub_nonneg.mpr hspectral

/-- Load-bearing step to prove: nonnegative spectral gap margin forces a lower
bound on the concrete boundary operator value. -/
def GapMarginToBoundaryLowerBound
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
    ∀ P : RamanujanAmplituhedronConcretePayload enc n L W,
      0 <= spectralGapMargin P ->
      n <= boundaryOperatorValue P

/-- If gap-to-boundary is proved, we get an explicit Cheeger certificate
builder (constructive form). -/
theorem cheegerCertificateBuilder_of_gapMargin
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (Hgap : GapMarginToBoundaryLowerBound enc n) :
    CheegerMixingCertificateBuilder enc n := by
  intro L W P hspectral
  have hmargin : 0 <= spectralGapMargin P :=
    spectralGapMargin_nonneg P hspectral
  exact ⟨Hgap L W P hmargin⟩

#print axioms spectralGapMargin_nonneg
#print axioms cheegerCertificateBuilder_of_gapMargin

end PallLean.Paper93.DeepMath.PathB
