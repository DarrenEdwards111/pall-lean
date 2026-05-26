import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWilliamsReflectionPlumbing
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDynamicExtractionDifficultyReduction

/-!
# Concrete discharge package

This file bundles the remaining obligations into one concrete package for a
chosen machine model and encoding, then derives end-to-end deep SAT search.
-/

namespace PallLean.Paper93.DeepMath.PathB

open SATDepthMachine
open PaperFaithfulSeparation

/-- Code-level reflection obligation for a fixed machine model and encoding. -/
def CodeDecisionReflection
    (U : MachineModel)
    (enc : ThreeCNFEncoding)
    (reflectCode : Nat -> TuringMachine.DTM) : Prop :=
  ∀ code : Nat,
    (∀ φ : CNF, U.decisionRun code φ = true ↔ Satisfiable φ) ->
      DTMDecidesSATWithEncoding enc (reflectCode code)

/-- Upgrade a code-level reflection theorem to a full reflection surface. -/
def reflectionSurface_of_codeReflection
    (U : MachineModel)
    (enc : ThreeCNFEncoding)
    (reflectCode : Nat -> TuringMachine.DTM)
    (hreflect : CodeDecisionReflection U enc reflectCode) :
    EncodedDTMDecisionReflectionSurface where
  U := U
  enc := enc
  reflectCode := reflectCode
  reflects_decider := hreflect

/-- Full concrete package of remaining obligations after all route plumbing. -/
structure ConcreteDischargePackage
    (U : MachineModel)
    (enc : ThreeCNFEncoding) where
  reflectCode : Nat -> TuringMachine.DTM
  reflect_correct : CodeDecisionReflection U enc reflectCode
  reduced_engine : DynamicExtractionDifficultyReducedEngine enc

/-- Main closure theorem from the concrete package. -/
theorem deepSATSearch_of_concreteDischargePackage
    (U : MachineModel)
    (enc : ThreeCNFEncoding)
    (P : ConcreteDischargePackage U enc) :
    DeepSATSearch U :=
  deepSATSearch_of_dynamicExtraction_and_reflectionSurface
    (reflectionSurface_of_codeReflection U enc P.reflectCode P.reflect_correct)
    (universalDynamicExtraction_of_difficultyReducedEngine enc P.reduced_engine)

/-! ## Axiom trace -/

#print axioms reflectionSurface_of_codeReflection
#print axioms deepSATSearch_of_concreteDischargePackage

end PallLean.Paper93.DeepMath.PathB
