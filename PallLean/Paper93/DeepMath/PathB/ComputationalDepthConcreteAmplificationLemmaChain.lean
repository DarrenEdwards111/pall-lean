import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConcreteExpansionPayload
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConcreteProgressLemmas

/-!
# Concrete amplification lemma chain

A minimal, non-vacuous theorem chain for the remaining core:

1. spectral/geometry assumptions on concrete-eligible witnesses;
2. boundary expansion lower bound;
3. binomial boundary-rank amplification.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Step A: concrete spectral/geometry condition at scale `n`. -/
abbrev ConcreteSpectralGeometryCondition
    (enc : ThreeCNFEncoding)
    (n : Nat) : Type :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
      RamanujanAmplituhedronExpansionPredicateConcrete enc n L W -> Prop

/-- Step B: spectral/geometry condition implies boundary-factor amplification. -/
def BoundaryExpansionFromSpectral
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (hS : ConcreteSpectralGeometryCondition enc n) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ W : DynamicMinorPreAmplificationWitness enc L n,
      ∀ hE : RamanujanAmplituhedronExpansionPredicateConcrete enc n L W,
        hS L W hE ->
        Nat.choose (n / 3) (Nat.log 2 n) <=
          L.toTrajectory.liveBoundaryRank n W.input W.time

/-- Step C: packaged concrete global amplification from a boundary-expansion
implication. -/
theorem concreteGlobalAmplification_of_boundaryExpansion
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (Hspec : ConcreteSpectralGeometryCondition enc n)
    (Hspec_realized :
      ∀ L : DynamicNFrameLagrangianObserver enc,
      ∀ W : DynamicMinorPreAmplificationWitness enc L n,
      ∀ hE : RamanujanAmplituhedronExpansionPredicateConcrete enc n L W,
        Hspec L W hE)
    (Hbound : BoundaryExpansionFromSpectral enc n Hspec) :
    RamanujanAmplituhedronGlobalAmplificationConcrete enc n := by
  intro L W hE
  exact Hbound L W hE (Hspec_realized L W hE)

/-- Builder-side obligation: chosen pre-witnesses are concrete-eligible. -/
def ConcreteEligibilityOfBuilder
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (buildPre : ThresholdLocalPreCandidateBuilder enc n) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ hthPre :
      (∃ W : DynamicMinorPreAmplificationWitness enc L n,
        0 < L.toTrajectory.liveBoundaryRank n W.input W.time),
      RamanujanAmplituhedronExpansionPredicateConcrete enc n L (buildPre L hthPre)

/-- If we have concrete global amplification and builder eligibility, we can
recover the local pre-level amplification socket needed by the main chain. -/
theorem thresholdLocalRankAmplificationPre_of_concreteGlobalAmplification
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (Hc : RamanujanAmplituhedronGlobalAmplificationConcrete enc n)
    (buildPre : ThresholdLocalPreCandidateBuilder enc n)
    (hbuild : ConcreteEligibilityOfBuilder enc n buildPre) :
    ThresholdLocalRankAmplificationPre enc n buildPre := by
  intro L hthPre
  exact Hc L (buildPre L hthPre) (hbuild L hthPre)

/-- If we have concrete global amplification and state-generator eligibility,
we recover the generator-side statewise rank amplification socket. -/
theorem statewiseRankAmplificationForGenerator_of_concreteGlobalAmplification
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (G : CoreWitnessAtStateGenerator enc n)
    (Hc : RamanujanAmplituhedronGlobalAmplificationConcrete enc n)
    (hgen :
      ∀ L : DynamicNFrameLagrangianObserver enc,
      ∀ input : Fin n -> Bool,
      ∀ time : Nat,
        RamanujanAmplituhedronExpansionPredicateConcrete
          enc n L (Classical.choose (G L input time))) :
    StatewiseRankAmplificationForGenerator enc n G := by
  intro L input time
  let W := Classical.choose (G L input time)
  exact Hc L W (by simpa [W] using hgen L input time)

#print axioms concreteGlobalAmplification_of_boundaryExpansion
#print axioms thresholdLocalRankAmplificationPre_of_concreteGlobalAmplification
#print axioms statewiseRankAmplificationForGenerator_of_concreteGlobalAmplification

end PallLean.Paper93.DeepMath.PathB
