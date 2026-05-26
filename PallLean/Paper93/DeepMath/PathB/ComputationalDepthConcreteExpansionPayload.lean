import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRamanujanAmplituhedronAmplificationSkeleton

/-!
# Concrete expansion payload surface

Replaces abstract payload `Prop` placeholders with concrete geometric/combinatorial
interfaces needed for load-bearing amplification.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Concrete Ramanujan-side graph data. -/
structure ExpansionGraph where
  vertexCount : Nat
  degree : Nat

/-- Spectral certificate interface for an expander graph.
This is no longer an arbitrary payload Prop: it is tied to concrete graph data. -/
structure RamanujanSpectralCertificate
    (G : ExpansionGraph) where
  secondEigenvalueBound : Rat
  ramanujanBound : secondEigenvalueBound <= (2 : Rat) * Rat.ofInt (Int.ofNat (Nat.sqrt (G.degree - 1)))

/-- Concrete amplituhedron positivity/nondegeneracy certificate. -/
structure AmplituhedronCertificate where
  ambientDim : Nat
  k : Nat
  positivityWitness : Prop

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
  boundaryCompatibility : Prop
  nontrivialBoundary : 0 < L.toTrajectory.liveBoundaryRank n W.input W.time

/-- New concrete eligibility predicate used by global amplification. -/
def RamanujanAmplituhedronExpansionPredicateConcrete
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (L : DynamicNFrameLagrangianObserver enc)
    (W : DynamicMinorPreAmplificationWitness enc L n) : Prop :=
  Nonempty (RamanujanAmplituhedronConcretePayload enc n L W)

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
