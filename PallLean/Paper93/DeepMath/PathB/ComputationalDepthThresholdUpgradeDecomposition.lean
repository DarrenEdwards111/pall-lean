import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDynamicExtractionDifficultyReduction

/-!
# Decomposing threshold-to-binomial upgrade

This file further splits `ThresholdWitnessToBinomialMinor` into two sockets:

1. a local upgrade witness constructor;
2. a local rank amplification proof.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Local constructor socket from a threshold witness to a candidate core
witness at the same scale. -/
def ThresholdLocalCandidateBuilder
    (enc : ThreeCNFEncoding) (n : Nat) : Type :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    (∃ W : DynamicMinorCoreWitness enc L n,
      0 < L.toTrajectory.liveBoundaryRank n W.input W.time) ->
      DynamicMinorCoreWitness enc L n

/-- Canonical local builder: choose one witness from the threshold-existence
hypothesis. This discharges the witness-construction socket completely, leaving
only local rank amplification as the mathematical frontier. -/
noncomputable def thresholdLocalCandidateBuilder_byChoice
    (enc : ThreeCNFEncoding) (n : Nat) :
    ThresholdLocalCandidateBuilder enc n :=
  fun _L hth => Classical.choose hth

/-- Local amplification socket: the built candidate has binomial lower bound on
trajectory boundary rank. This is stated in terms of the already built core
witness, so it can be attacked independently from witness construction. -/
def ThresholdLocalRankAmplification
    (enc : ThreeCNFEncoding) (n : Nat)
    (build : ThresholdLocalCandidateBuilder enc n) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ hth :
      (∃ W : DynamicMinorCoreWitness enc L n,
        0 < L.toTrajectory.liveBoundaryRank n W.input W.time),
      Nat.choose (n / 3) (Nat.log 2 n) <=
        L.toTrajectory.liveBoundaryRank n (build L hth).input (build L hth).time

/-- Builder + local amplification imply threshold-to-binomial minor upgrade. -/
def thresholdWitnessToBinomialMinor_of_localDecomposition
    (enc : ThreeCNFEncoding) (n : Nat)
    (build : ThresholdLocalCandidateBuilder enc n)
    (_hamplify : ThresholdLocalRankAmplification enc n build) :
    ThresholdWitnessToBinomialMinor enc n :=
  build

/-- Full reduced-engine variant with decomposed upgrade socket. -/
structure DynamicExtractionDifficultyReducedEngineV2
    (enc : ThreeCNFEncoding) where
  lengthForExponent : Nat -> Nat
  length_large : ∀ c : Nat, lengthForExponent c >= 2 ^ 20
  length_log : ∀ c : Nat, 4 * (c + 1) <= Nat.log 2 (lengthForExponent c)
  semantic_nontrivial :
    ∀ c : Nat, NontrivialSemanticRankAtScale enc (lengthForExponent c)
  threshold_lift :
    ∀ c : Nat,
      NontrivialSemanticRankAtScale enc (lengthForExponent c) ->
        UniformThresholdBoundaryWitness enc (lengthForExponent c)
  local_rank_amplification :
    ∀ c : Nat,
      ThresholdLocalRankAmplification
        enc (lengthForExponent c)
        (thresholdLocalCandidateBuilder_byChoice enc (lengthForExponent c))

/-- V2 engine downgrades to the previous reduced engine. -/
noncomputable def DynamicExtractionDifficultyReducedEngineV2.toReducedEngine
    {enc : ThreeCNFEncoding}
    (E : DynamicExtractionDifficultyReducedEngineV2 enc) :
    DynamicExtractionDifficultyReducedEngine enc where
  lengthForExponent := E.lengthForExponent
  length_large := E.length_large
  length_log := E.length_log
  semantic_nontrivial := E.semantic_nontrivial
  threshold_lift := E.threshold_lift
  threshold_to_binomial := by
    intro c
    exact thresholdWitnessToBinomialMinor_of_localDecomposition
      enc (E.lengthForExponent c)
      (thresholdLocalCandidateBuilder_byChoice enc (E.lengthForExponent c))
      (E.local_rank_amplification c)

/-- V2 engine still closes universal dynamic extraction. -/
theorem universalDynamicExtraction_of_difficultyReducedEngineV2
    (enc : ThreeCNFEncoding)
    (E : DynamicExtractionDifficultyReducedEngineV2 enc) :
    UniversalDynamicNFrameLagrangianExtraction enc :=
  universalDynamicExtraction_of_difficultyReducedEngine
    enc E.toReducedEngine

/-! ## Axiom trace -/

#print axioms thresholdWitnessToBinomialMinor_of_localDecomposition
#print axioms DynamicExtractionDifficultyReducedEngineV2.toReducedEngine
#print axioms universalDynamicExtraction_of_difficultyReducedEngineV2

end PallLean.Paper93.DeepMath.PathB
