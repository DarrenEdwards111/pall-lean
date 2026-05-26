import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSpectralBoundaryOperatorSkeleton

/-!
# Spectral-gap core decomposition

Isolates the remaining hard theorem into explicit sub-obligations:
- a concrete Ramanujan/mixing lower bound on boundary edge count,
- a combinatorial comparison from that lower bound to the binomial target.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Sub-obligation A: concrete Ramanujan/mixing estimate on boundary edges. -/
def RamanujanMixingBoundaryLowerBound
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
    ∀ P : RamanujanAmplituhedronConcretePayload enc n L W,
      P.spectral.secondEigenvalueBound <=
        (2 : Rat) * Rat.ofInt (Int.ofNat (Nat.sqrt (P.expanderGraph.degree - 1))) ->
      n <= boundaryEdgeCount P

/-- Sub-obligation B: combinatorial growth from `n` to the binomial target. -/
def BinomialTargetBelowLinearBoundary
    (n : Nat) : Prop :=
  Nat.choose (n / 3) (Nat.log 2 n) <= n

/-- Core theorem assembly: if A and B hold, the hard spectral-to-boundary-count
statement follows. -/
theorem spectralGapImpliesBoundaryCountLowerBound_of_core
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (Hmix : RamanujanMixingBoundaryLowerBound enc n)
    (Hbin : BinomialTargetBelowLinearBoundary n) :
    SpectralGapImpliesBoundaryCountLowerBound enc n := by
  intro L W P hspectral
  exact le_trans Hbin (Hmix L W P hspectral)

/-- End-to-end closure of the currently open core route: proving A+B discharges
`SpectralToExpansionFactorLowerBound`. -/
theorem spectralToExpansionFactor_of_coreDecomposition
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (Hmix : RamanujanMixingBoundaryLowerBound enc n)
    (Hbin : BinomialTargetBelowLinearBoundary n) :
    SpectralToExpansionFactorLowerBound enc n :=
  spectralToExpansionFactor_of_boundaryOperatorChain
    enc n
    (spectralGapImpliesBoundaryCountLowerBound_of_core enc n Hmix Hbin)
    (boundaryCountToDerivedExpansionLowerBound_trivial enc n)

#print axioms spectralGapImpliesBoundaryCountLowerBound_of_core
#print axioms spectralToExpansionFactor_of_coreDecomposition

end PallLean.Paper93.DeepMath.PathB
