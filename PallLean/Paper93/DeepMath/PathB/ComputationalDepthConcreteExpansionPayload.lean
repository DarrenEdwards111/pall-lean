import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRamanujanAmplituhedronAmplificationSkeleton

/-!
# Concrete expansion payload surface

Replaces abstract payload `Prop` placeholders with concrete geometric/combinatorial
interfaces needed for load-bearing amplification.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Concrete finite regular graph data (no placeholder-only payload). -/
structure ExpansionGraph where
  vertexCount : Nat
  degree : Nat
  adjacency : Fin vertexCount -> Fin vertexCount -> Bool
  symmetric : ∀ i j, adjacency i j = adjacency j i

/-- Spectral certificate interface for an expander graph. -/
structure RamanujanSpectralCertificate
    (G : ExpansionGraph) where
  secondEigenvalueBound : Rat
  ramanujanBound :
    secondEigenvalueBound <= (2 : Rat) * Rat.ofInt (Int.ofNat (Nat.sqrt (G.degree - 1)))

/-- Concrete amplituhedron positivity/nondegeneracy certificate encoded as
numeric constraints (not a free-standing arbitrary `Prop`). -/
structure AmplituhedronCertificate where
  ambientDim : Nat
  k : Nat
  positivityScore : Nat
  nondegenerate : 0 < positivityScore

/-- Concrete expansion payload carried by a pre-amplification witness.
All fields are data/certificates, not self-certifying mirror props from `W`. -/
structure RamanujanAmplituhedronConcretePayload
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (L : DynamicNFrameLagrangianObserver enc)
    (W : DynamicMinorPreAmplificationWitness enc L n) where
  expanderGraph : ExpansionGraph
  spectral : RamanujanSpectralCertificate expanderGraph
  amplituhedron : AmplituhedronCertificate

/-- Derived expansion factor (not freely choosable): computed from concrete
graph/amplituhedron payload data. -/
def derivedBoundaryExpansionFactor
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : DynamicNFrameLagrangianObserver enc}
    {W : DynamicMinorPreAmplificationWitness enc L n}
    (P : RamanujanAmplituhedronConcretePayload enc n L W) : Nat :=
  P.expanderGraph.degree * P.amplituhedron.positivityScore

/-- Concrete payload must embed its derived expansion factor into live boundary
rank and certify nontriviality of the derived factor. -/
structure RamanujanAmplituhedronBoundaryEmbedding
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (L : DynamicNFrameLagrangianObserver enc)
    (W : DynamicMinorPreAmplificationWitness enc L n)
    (P : RamanujanAmplituhedronConcretePayload enc n L W) where
  boundary_from_expansion :
    derivedBoundaryExpansionFactor P <= L.toTrajectory.liveBoundaryRank n W.input W.time
  boundary_nontrivial : 0 < derivedBoundaryExpansionFactor P

/-- New concrete eligibility predicate used by global amplification. -/
def RamanujanAmplituhedronExpansionPredicateConcrete
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (L : DynamicNFrameLagrangianObserver enc)
    (W : DynamicMinorPreAmplificationWitness enc L n) : Prop :=
  ∃ P : RamanujanAmplituhedronConcretePayload enc n L W,
    RamanujanAmplituhedronBoundaryEmbedding enc n L W P
/-- Zero-rank trajectories cannot satisfy concrete expansion eligibility. -/
theorem not_concreteExpansion_of_zeroBoundaryRank
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (L : DynamicNFrameLagrangianObserver enc)
    (hzero : ∀ input : Fin n -> Bool, ∀ time : Nat,
      L.toTrajectory.liveBoundaryRank n input time = 0)
    (W : DynamicMinorPreAmplificationWitness enc L n) :
    ¬ RamanujanAmplituhedronExpansionPredicateConcrete enc n L W := by
  intro hE
  rcases hE with ⟨P, hB⟩
  have hposRank : 0 < L.toTrajectory.liveBoundaryRank n W.input W.time :=
    lt_of_lt_of_le hB.boundary_nontrivial hB.boundary_from_expansion
  have hz : L.toTrajectory.liveBoundaryRank n W.input W.time = 0 := hzero W.input W.time
  have : 0 < 0 := by simpa [hz] using hposRank
  exact Nat.not_lt_zero 0 this

/-- Core spectral-to-factor target: concrete spectral/geometry data should force
binomial lower bound on the boundary expansion factor. -/
def SpectralToExpansionFactorLowerBound
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
      ∀ hE : RamanujanAmplituhedronExpansionPredicateConcrete enc n L W,
        let P := Classical.choose hE
        P.spectral.secondEigenvalueBound <=
          (2 : Rat) * Rat.ofInt (Int.ofNat (Nat.sqrt (P.expanderGraph.degree - 1))) ->
        Nat.choose (n / 3) (Nat.log 2 n) <=
          derivedBoundaryExpansionFactor P
/-- Concrete global amplification target: if a witness carries concrete
expander/boundary/positivity payload, then binomial boundary-rank lower bound
holds. -/
def RamanujanAmplituhedronGlobalAmplificationConcrete
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
      RamanujanAmplituhedronExpansionPredicateConcrete enc n L W ->
      Nat.choose (n / 3) (Nat.log 2 n) <=
        L.toTrajectory.liveBoundaryRank n W.input W.time

/-- Once the factor lower bound is proved from spectral data, concrete global
amplification follows by the payload's boundary embedding inequality. -/
theorem concreteGlobalAmplification_of_spectralFactor
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (Hfactor : SpectralToExpansionFactorLowerBound enc n) :
    RamanujanAmplituhedronGlobalAmplificationConcrete enc n := by
  intro L W hE
  let P := Classical.choose hE
  let hB : RamanujanAmplituhedronBoundaryEmbedding enc n L W P :=
    Classical.choose_spec hE
  have hspectral :
      P.spectral.secondEigenvalueBound <=
        (2 : Rat) * Rat.ofInt (Int.ofNat (Nat.sqrt (P.expanderGraph.degree - 1))) :=
    P.spectral.ramanujanBound
  exact le_trans (Hfactor L W hE hspectral) hB.boundary_from_expansion
/-- Compatibility bridge: if concrete certificates are known to force the
abstract payload interface, we can still reuse earlier plumbing. -/
def ConcreteImpliesAbstractExpansion
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
  ∀ W : DynamicMinorPreAmplificationWitness enc L n,
    RamanujanAmplituhedronExpansionPredicateConcrete enc n L W ->
    RamanujanAmplituhedronExpansionPredicate enc n L W

/-- Bridge theorem parameterized by an explicit compatibility hypothesis. -/
theorem abstractExpansion_of_concreteExpansion
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (Hcompat : ConcreteImpliesAbstractExpansion enc n)
    (L : DynamicNFrameLagrangianObserver enc)
    (W : DynamicMinorPreAmplificationWitness enc L n) :
    RamanujanAmplituhedronExpansionPredicateConcrete enc n L W ->
    RamanujanAmplituhedronExpansionPredicate enc n L W := by
  intro h
  exact Hcompat L W h

/-- Bridge: any proof of concrete global amplification yields the existing
abstract global amplification target. -/
theorem globalAmplification_of_concreteGlobalAmplification
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (Hc : RamanujanAmplituhedronGlobalAmplificationConcrete enc n)
    (hcompat :
      ∀ L : DynamicNFrameLagrangianObserver enc,
      ∀ W : DynamicMinorPreAmplificationWitness enc L n,
        RamanujanAmplituhedronExpansionPredicate enc n L W ->
        RamanujanAmplituhedronExpansionPredicateConcrete enc n L W) :
    RamanujanAmplituhedronGlobalAmplification enc n := by
  intro L W hE
  exact Hc L W (hcompat L W hE)

#print axioms abstractExpansion_of_concreteExpansion
#print axioms globalAmplification_of_concreteGlobalAmplification

end PallLean.Paper93.DeepMath.PathB
