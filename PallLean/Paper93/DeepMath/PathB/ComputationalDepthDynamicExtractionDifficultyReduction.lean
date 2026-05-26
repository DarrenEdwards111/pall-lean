import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDynamicExtractionBlueprint

/-!
# Difficulty-reduced decomposition for dynamic extraction

This file splits the monolithic `extract_core` obligation into three strictly
scoped sockets:

1. semantic nontriviality at scale,
2. uniform threshold boundary witness,
3. threshold-to-minor upgrade.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Step 1: semantic nontriviality signal at a chosen scale. -/
def NontrivialSemanticRankAtScale
    (enc : ThreeCNFEncoding) (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∃ input : Fin n -> Bool,
      ∃ time : Nat,
        0 < L.toTrajectory.liveBoundaryRank n input time

/-- Step 2: uniform threshold witness from nontrivial semantic rank. -/
def UniformThresholdBoundaryWitness
    (enc : ThreeCNFEncoding) (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∃ W : DynamicMinorCoreWitness enc L n,
      0 < L.toTrajectory.liveBoundaryRank n W.input W.time

/-- Step 3: upgrade threshold witness to full binomial-rank core witness. -/
def ThresholdWitnessToBinomialMinor
    (enc : ThreeCNFEncoding) (n : Nat) : Type :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    (∃ W : DynamicMinorCoreWitness enc L n,
      0 < L.toTrajectory.liveBoundaryRank n W.input W.time) ->
      DynamicMinorCoreWitness enc L n

/-- Reduced engine: numeric length bounds plus the two intermediate sockets and
final upgrade socket. -/
structure DynamicExtractionDifficultyReducedEngine
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
  threshold_to_binomial :
    ∀ c : Nat,
      ThresholdWitnessToBinomialMinor enc (lengthForExponent c)

/-- Convert the reduced engine into the core extraction engine. -/
def DynamicExtractionDifficultyReducedEngine.toCoreEngine
    {enc : ThreeCNFEncoding}
    (E : DynamicExtractionDifficultyReducedEngine enc) :
    DynamicNFrameLagrangianCoreExtractionEngine enc where
  lengthForExponent := E.lengthForExponent
  length_large := E.length_large
  length_log := E.length_log
  extract_core := by
    intro c L
    have hnontriv : NontrivialSemanticRankAtScale enc (E.lengthForExponent c) :=
      E.semantic_nontrivial c
    have hthresh : UniformThresholdBoundaryWitness enc (E.lengthForExponent c) :=
      E.threshold_lift c hnontriv
    have hExists :
        ∃ W : DynamicMinorCoreWitness enc L (E.lengthForExponent c),
          0 < L.toTrajectory.liveBoundaryRank
            (E.lengthForExponent c) W.input W.time :=
      hthresh L
    exact E.threshold_to_binomial c L hExists

/-- Therefore a reduced engine is enough to prove universal dynamic extraction.
-/
theorem universalDynamicExtraction_of_difficultyReducedEngine
    (enc : ThreeCNFEncoding)
    (E : DynamicExtractionDifficultyReducedEngine enc) :
    UniversalDynamicNFrameLagrangianExtraction enc :=
  universalDynamicExtraction_of_coreEngine enc E.toCoreEngine

/-! ## Axiom trace -/

#print axioms DynamicExtractionDifficultyReducedEngine.toCoreEngine
#print axioms universalDynamicExtraction_of_difficultyReducedEngine

end PallLean.Paper93.DeepMath.PathB
