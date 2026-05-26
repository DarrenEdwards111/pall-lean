import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConcreteDischargePackage
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLoadBearingAmplification
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRamanujanAmplituhedronAmplificationSkeleton

/-!
# Concrete progress lemmas toward full discharge

This file discharges two frontier sockets modulo explicit local generators,
shrinking the remaining proof target to one geometric/rank core.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation
open SATDepthMachine

/-- Local core witness generator from trajectory state.

Given an observer, length, input, and time, produce a core witness anchored at
that state (same `input` and `time`). This isolates SAT/encoding/payload
construction from rank bounds. -/
def CoreWitnessAtStateGenerator
    (enc : ThreeCNFEncoding) (n : Nat) : Prop :=
  ∀ L : DynamicNFrameLagrangianObserver enc,
    ∀ input : Fin n -> Bool,
      ∀ time : Nat,
        ∃ W : DynamicMinorCoreWitness enc L n,
          W.input = input ∧ W.time = time

/-- `threshold_lift` discharges from nontrivial rank plus a local state witness
generator. -/
theorem thresholdLift_of_coreWitnessAtStateGenerator
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (G : CoreWitnessAtStateGenerator enc n) :
    NontrivialSemanticRankAtScale enc n ->
      UniformThresholdBoundaryWitness enc n := by
  intro hnontriv
  intro L
  rcases hnontriv L with ⟨input, time, hpos⟩
  rcases G L input time with ⟨W, hWin, hWtime⟩
  refine ⟨W, ?_⟩
  simpa [hWin, hWtime] using hpos

/-- A concrete near-final package: reflection is discharged, semantic-nontrivial
and threshold-lift are discharged, and local rank amplification is reduced to
Ramanujan/amplituhedron hypotheses. -/
structure ConcreteNearFinalPackage
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
  pre_builder :
    ∀ c : Nat,
      ThresholdLocalPreCandidateBuilder enc (lengthForExponent c)
  ramanujan_amplituhedron_hypotheses :
    ∀ c : Nat,
      RamanujanAmplituhedronAmplificationHypotheses
        enc (lengthForExponent c) (pre_builder c)

/-- Near-final package reduces the whole route to the Ramanujan/amplituhedron
local rank theorem at each exponent scale. -/
theorem deepSATSearch_of_concreteNearFinalPackage
    (U : MachineModel)
    (enc : ThreeCNFEncoding)
    (P : ConcreteNearFinalPackage U enc) :
    DeepSATSearch U := by
  let E : DynamicExtractionDifficultyReducedEngine enc := {
    lengthForExponent := P.lengthForExponent
    length_large := P.length_large
    length_log := P.length_log
    semantic_nontrivial := P.semantic_nontrivial
    threshold_lift := by
      intro c hnontriv
      exact thresholdLift_of_coreWitnessAtStateGenerator
        enc (P.lengthForExponent c) (P.core_witness_generator c) hnontriv
    threshold_to_binomial := by
      intro c
      let buildPre := P.pre_builder c
      let hamplifyPre :=
        thresholdLocalRankAmplificationPre_of_ramanujanAmplituhedron
          enc (P.lengthForExponent c) buildPre
          (P.ramanujan_amplituhedron_hypotheses c)
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

#print axioms thresholdLift_of_coreWitnessAtStateGenerator
#print axioms deepSATSearch_of_concreteNearFinalPackage

end PallLean.Paper93.DeepMath.PathB
