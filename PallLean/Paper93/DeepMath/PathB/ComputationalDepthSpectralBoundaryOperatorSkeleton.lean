import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConcreteExpansionPayload

/-!
# Spectral boundary-operator skeleton

Concrete next-step scaffold:
1) boundary operator/count definitions,
2) spectral-gap to expansion lower bound target,
3) transfer to derived boundary expansion factor target.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Boundary edge count induced by graph adjacency and witness input labels. -/
def boundaryEdgeCount
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : DynamicNFrameLagrangianObserver enc}
    {W : DynamicMinorPreAmplificationWitness enc L n}
    (P : RamanujanAmplituhedronConcretePayload enc n L W) : Nat :=
  P.expanderGraph.degree * P.amplituhedron.positivityScore

/-- Normalized boundary expansion ratio (combinatorial placeholder). -/
def boundaryExpansionRatio
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : DynamicNFrameLagrangianObserver enc}
    {W : DynamicMinorPreAmplificationWitness enc L n}
    (P : RamanujanAmplituhedronConcretePayload enc n L W) : Rat :=
  if h : P.expanderGraph.vertexCount = 0 then 0
  else Rat.ofInt (Int.ofNat (boundaryEdgeCount P)) / Rat.ofInt (Int.ofNat P.expanderGraph.vertexCount)

/-- Target theorem statement: Ramanujan spectral condition implies a lower bound
on the combinatorial boundary count. -/
def SpectralGapImpliesBoundaryCountLowerBound
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
    ∀ P : RamanujanAmplituhedronConcretePayload enc n L W,
      P.spectral.secondEigenvalueBound <=
        (2 : Rat) * Rat.ofInt (Int.ofNat (Nat.sqrt (P.expanderGraph.degree - 1))) ->
      Nat.choose (n / 3) (Nat.log 2 n) <= boundaryEdgeCount P

/-- Target theorem statement: boundary count lower bound transfers to the
payload's derived expansion factor. -/
def BoundaryCountToDerivedExpansionLowerBound
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
    ∀ P : RamanujanAmplituhedronConcretePayload enc n L W,
      Nat.choose (n / 3) (Nat.log 2 n) <= boundaryEdgeCount P ->
      Nat.choose (n / 3) (Nat.log 2 n) <= derivedBoundaryExpansionFactor P

/-- Bridge: proving the two concrete targets discharges
`SpectralToExpansionFactorLowerBound`. -/
theorem spectralToExpansionFactor_of_boundaryOperatorChain
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (Hspec : SpectralGapImpliesBoundaryCountLowerBound enc n)
    (Htransfer : BoundaryCountToDerivedExpansionLowerBound enc n) :
    SpectralToExpansionFactorLowerBound enc n := by
  intro L W hE
  dsimp
  intro hspectral
  let P := Classical.choose hE
  have hCount : Nat.choose (n / 3) (Nat.log 2 n) <= boundaryEdgeCount P :=
    Hspec L W P hspectral
  exact Htransfer L W P hCount

#print axioms spectralToExpansionFactor_of_boundaryOperatorChain

end PallLean.Paper93.DeepMath.PathB
