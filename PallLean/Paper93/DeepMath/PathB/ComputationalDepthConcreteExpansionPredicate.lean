import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConcreteProgressLemmas

/-!
# Concrete expansion predicate for the Ramanujan/amplituhedron socket

The previous expansion gate was intentionally abstract: it read the payload
fields already stored on the witness.  This file introduces a concrete
rank-certificate predicate, so expansion eligibility is not automatically true
from witness construction.

The certificate still contains the hard mathematics as an explicit embedding
claim.  The point is sharper localization: zero-rank presentations cannot
satisfy the predicate, and the final route can require concrete expansion
eligibility rather than self-realized payload props.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation
open SATDepthMachine

/-- Concrete expansion certificate.

`expandedBoundaryRank` is the rank carried by the Ramanujan/amplituhedron
boundary expansion mechanism.  The two inequalities say that this expanded
rank is large enough for the binomial minor and embeds into the observer's
actual live boundary rank at the same input/time. -/
structure ConcreteRamanujanAmplituhedronExpansionCertificate
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (L : DynamicNFrameLagrangianObserver enc)
    (W : DynamicMinorPreAmplificationWitness enc L n) where
  expandedBoundaryRank : Nat
  ramanujanSpectralGapWitness : Nat
  spectralGap_positive : 0 < ramanujanSpectralGapWitness
  binomial_le_expandedBoundaryRank :
    Nat.choose (n / 3) (Nat.log 2 n) <= expandedBoundaryRank
  expandedBoundaryRank_le_liveBoundaryRank :
    expandedBoundaryRank <=
      L.toTrajectory.liveBoundaryRank n W.input W.time

/-- Non-vacuous expansion predicate: there is concrete spectral/rank data
embedding a binomial-size expanded boundary into the live boundary rank. -/
def ConcreteRamanujanAmplituhedronExpansionPredicate
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (L : DynamicNFrameLagrangianObserver enc)
    (W : DynamicMinorPreAmplificationWitness enc L n) : Prop :=
  Nonempty (ConcreteRamanujanAmplituhedronExpansionCertificate enc n L W)

/-- Concrete expansion immediately gives the binomial live-rank lower bound. -/
theorem rankLower_of_concreteRamanujanAmplituhedronExpansion
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : DynamicNFrameLagrangianObserver enc}
    {W : DynamicMinorPreAmplificationWitness enc L n}
    (h :
      ConcreteRamanujanAmplituhedronExpansionPredicate enc n L W) :
    Nat.choose (n / 3) (Nat.log 2 n) <=
      L.toTrajectory.liveBoundaryRank n W.input W.time := by
  rcases h with ⟨C⟩
  exact Nat.le_trans
    C.binomial_le_expandedBoundaryRank
    C.expandedBoundaryRank_le_liveBoundaryRank

/-- A zero-rank presentation cannot be expansion-eligible at a scale where the
binomial minor has positive size. -/
theorem not_concreteExpansion_of_zero_liveBoundaryRank
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : DynamicNFrameLagrangianObserver enc}
    {W : DynamicMinorPreAmplificationWitness enc L n}
    (hbin : 0 < Nat.choose (n / 3) (Nat.log 2 n))
    (hzero : L.toTrajectory.liveBoundaryRank n W.input W.time = 0) :
    ¬ ConcreteRamanujanAmplituhedronExpansionPredicate enc n L W := by
  intro h
  have hle :
      Nat.choose (n / 3) (Nat.log 2 n) <= 0 := by
    simpa [hzero] using
      rankLower_of_concreteRamanujanAmplituhedronExpansion h
  exact (Nat.not_lt_of_ge hle) hbin

/-- Concrete expansion eligibility for the pre-builder discharges the pre-level
rank-amplification socket. -/
theorem thresholdLocalRankAmplificationPre_of_concreteExpansion
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (buildPre : ThresholdLocalPreCandidateBuilder enc n)
    (hbuild_expands :
      ∀ L : DynamicNFrameLagrangianObserver enc,
      ∀ hthPre :
        (∃ W : DynamicMinorPreAmplificationWitness enc L n,
          0 < L.toTrajectory.liveBoundaryRank n W.input W.time),
        ConcreteRamanujanAmplituhedronExpansionPredicate
          enc n L (buildPre L hthPre)) :
    ThresholdLocalRankAmplificationPre enc n buildPre := by
  intro L hthPre
  exact rankLower_of_concreteRamanujanAmplituhedronExpansion
    (hbuild_expands L hthPre)

/-- Concrete expansion eligibility for generated state witnesses discharges the
statewise amplification socket. -/
theorem statewiseRankAmplificationForGenerator_of_concreteExpansion
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (G : CoreWitnessAtStateGenerator enc n)
    (hgen_expands :
      ∀ L : DynamicNFrameLagrangianObserver enc,
      ∀ input : Fin n -> Bool,
      ∀ time : Nat,
        ConcreteRamanujanAmplituhedronExpansionPredicate
          enc n L (Classical.choose (G L input time))) :
    StatewiseRankAmplificationForGenerator enc n G := by
  intro L input time
  exact rankLower_of_concreteRamanujanAmplituhedronExpansion
    (hgen_expands L input time)

/-- Near-final package using only concrete expansion eligibility, not the older
self-realized payload conjunction. -/
structure ConcreteExpansionNearFinalPackage
    (U : MachineModel)
    (enc : ThreeCNFEncoding) where
  reflectCode : Nat -> TuringMachine.DTM
  reflect_correct : CodeDecisionReflection U enc reflectCode
  lengthForExponent : Nat -> Nat
  length_large : ∀ c : Nat, lengthForExponent c >= 2 ^ 20
  length_log : ∀ c : Nat, 4 * (c + 1) <= Nat.log 2 (lengthForExponent c)
  semantic_nontrivial :
    ∀ c : Nat, NontrivialSemanticRankAtScale enc (lengthForExponent c)
  core_witness_generator :
    ∀ c : Nat,
      CoreWitnessAtStateGenerator enc (lengthForExponent c)
  generated_witness_expands :
    ∀ c : Nat,
      ∀ L : DynamicNFrameLagrangianObserver enc,
      ∀ input : Fin (lengthForExponent c) -> Bool,
      ∀ time : Nat,
        ConcreteRamanujanAmplituhedronExpansionPredicate
          enc (lengthForExponent c) L
          (Classical.choose (core_witness_generator c L input time))
  pre_builder :
    ∀ c : Nat,
      ThresholdLocalPreCandidateBuilder enc (lengthForExponent c)
  pre_builder_expands :
    ∀ c : Nat,
      ∀ L : DynamicNFrameLagrangianObserver enc,
      ∀ hthPre :
        (∃ W : DynamicMinorPreAmplificationWitness enc L (lengthForExponent c),
          0 < L.toTrajectory.liveBoundaryRank
            (lengthForExponent c) W.input W.time),
        ConcreteRamanujanAmplituhedronExpansionPredicate
          enc (lengthForExponent c) L (pre_builder c L hthPre)

/-- Final routing from the concrete expansion package.  The only rank-bearing
content now lives in the concrete expansion certificates supplied by the
package fields. -/
theorem deepSATSearch_of_concreteExpansionNearFinalPackage
    (U : MachineModel)
    (enc : ThreeCNFEncoding)
    (P : ConcreteExpansionNearFinalPackage U enc) :
    DeepSATSearch U := by
  let E : DynamicExtractionDifficultyReducedEngine enc := {
    lengthForExponent := P.lengthForExponent
    length_large := P.length_large
    length_log := P.length_log
    semantic_nontrivial := P.semantic_nontrivial
    threshold_lift := by
      intro c hnontriv
      exact thresholdLift_of_coreWitnessAtStateGenerator
        enc (P.lengthForExponent c)
        (P.core_witness_generator c)
        (statewiseRankAmplificationForGenerator_of_concreteExpansion
          enc (P.lengthForExponent c)
          (P.core_witness_generator c)
          (P.generated_witness_expands c))
        hnontriv
    threshold_to_binomial := by
      intro c
      let buildPre := P.pre_builder c
      let hamplifyPre :=
        thresholdLocalRankAmplificationPre_of_concreteExpansion
          enc (P.lengthForExponent c) buildPre
          (P.pre_builder_expands c)
      let buildCore := thresholdLocalCandidateBuilder_fromPre
        enc (P.lengthForExponent c) buildPre hamplifyPre
      let hamplifyCore := thresholdLocalRankAmplification_of_preAmplification
        enc (P.lengthForExponent c) buildPre hamplifyPre
      exact thresholdWitnessToBinomialMinor_of_localDecomposition
        enc (P.lengthForExponent c) buildCore hamplifyCore
  }
  exact deepSATSearch_of_concreteDischargePackage U enc {
    reflectCode := P.reflectCode
    reflect_correct := P.reflect_correct
    reduced_engine := E
  }

/-! ## Axiom trace -/

#print axioms rankLower_of_concreteRamanujanAmplituhedronExpansion
#print axioms not_concreteExpansion_of_zero_liveBoundaryRank
#print axioms thresholdLocalRankAmplificationPre_of_concreteExpansion
#print axioms statewiseRankAmplificationForGenerator_of_concreteExpansion
#print axioms deepSATSearch_of_concreteExpansionNearFinalPackage

end PallLean.Paper93.DeepMath.PathB
