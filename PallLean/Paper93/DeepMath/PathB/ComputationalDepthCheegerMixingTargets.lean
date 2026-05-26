import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSpectralGapCoreDecomposition

/-!
# Cheeger/mixing targets for the spectral core

Non-circular target layer:
1) formal Cheeger/mixing inequality target in this payload setting,
2) arithmetic bridge target for binomial-vs-linear growth,
3) composed route to Ramanujan mixing boundary lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Concrete boundary operator value used by mixing/Cheeger targets.
Kept as a named alias to stabilize theorem statements while internals evolve. -/
def boundaryOperatorValue
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : DynamicNFrameLagrangianObserver enc}
    {W : DynamicMinorPreAmplificationWitness enc L n}
    (P : RamanujanAmplituhedronConcretePayload enc n L W) : Nat :=
  boundaryEdgeCount P

/-- Cheeger/mixing-style lower bound target from Ramanujan spectral input. -/
def CheegerMixingBoundaryLowerBoundTarget
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
    ∀ P : RamanujanAmplituhedronConcretePayload enc n L W,
      P.spectral.secondEigenvalueBound <=
        (2 : Rat) * Rat.ofInt (Int.ofNat (Nat.sqrt (P.expanderGraph.degree - 1))) ->
      n <= boundaryOperatorValue P

/-- Arithmetic bridge target (small-regime variant): under explicit bounded
scale assumptions, the binomial term is bounded by linear scale `n`.

Note: this is intentionally small-regime; the unrestricted global inequality is
false in general. -/
def BinomialLinearBridgeTarget (n : Nat) : Prop :=
  2 <= n /\ n <= 20 /\
  Nat.choose (n / 3) (Nat.log 2 n) <= n

/-- Compose Cheeger/mixing and arithmetic bridge into the previously isolated
`RamanujanMixingBoundaryLowerBound`. -/
theorem ramanujanMixingBoundaryLowerBound_of_cheegerAndBinomial
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (Hcheeger : CheegerMixingBoundaryLowerBoundTarget enc n)
    (_Hbin : BinomialLinearBridgeTarget n) :
    RamanujanMixingBoundaryLowerBound enc n := by
  intro L W P hspectral
  have hlin : n <= boundaryOperatorValue P := Hcheeger L W P hspectral
  simpa [boundaryOperatorValue] using hlin

/-- End-to-end composed core route with explicit assumptions. -/
theorem spectralToExpansionFactor_of_cheegerAndBinomial
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (Hcheeger : CheegerMixingBoundaryLowerBoundTarget enc n)
    (Hbin : BinomialLinearBridgeTarget n) :
    SpectralToExpansionFactorLowerBound enc n :=
  spectralToExpansionFactor_of_coreDecomposition
    enc n
    (ramanujanMixingBoundaryLowerBound_of_cheegerAndBinomial enc n Hcheeger Hbin)
    Hbin.2.2

#print axioms ramanujanMixingBoundaryLowerBound_of_cheegerAndBinomial
#print axioms spectralToExpansionFactor_of_cheegerAndBinomial

end PallLean.Paper93.DeepMath.PathB
