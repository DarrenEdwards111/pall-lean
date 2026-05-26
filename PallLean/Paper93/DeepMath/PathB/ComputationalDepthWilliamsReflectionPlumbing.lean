import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWilliamsPACFinalDischarge

/-!
# Concrete reflection plumbing for Item 1

This file isolates the model-plumbing needed to instantiate
`SATDecisionReflectionToEncodedDTM` for a concrete machine model.
-/

namespace PallLean.Paper93.DeepMath.PathB

open SATDepthMachine

/-- A concrete model-level reflection surface:

* `U` is the SAT decision/search machine model used on the Williams side.
* `enc` is the encoded DTM SAT surface used on the PAC/Lagrangian side.
* `reflectCode` maps decision codes in `U` to concrete DTMs.
* `reflects_decider` is the load-bearing correctness obligation.
-/
structure EncodedDTMDecisionReflectionSurface where
  U : MachineModel
  enc : ThreeCNFEncoding
  reflectCode : Nat -> TuringMachine.DTM
  reflects_decider :
    ∀ code : Nat,
      (∀ φ : CNF, U.decisionRun code φ = true ↔ Satisfiable φ) ->
        DTMDecidesSATWithEncoding enc (reflectCode code)

/-- Any model-level reflection surface yields the required
`SATDecisionReflectionToEncodedDTM` interface. -/
def satDecisionReflection_of_surface
    (S : EncodedDTMDecisionReflectionSurface) :
    SATDecisionReflectionToEncodedDTM S.U S.enc where
  reflect := fun D => S.reflectCode D.code
  reflects_correct := by
    intro D hD
    exact S.reflects_decider D.code hD

/-- Plugging a reflection surface into universal dynamic N-frame/Lagrangian
extraction closes deep SAT search for that machine model. -/
theorem deepSATSearch_of_dynamicExtraction_and_reflectionSurface
    (S : EncodedDTMDecisionReflectionSurface)
    (hextract : UniversalDynamicNFrameLagrangianExtraction S.enc) :
    DeepSATSearch S.U :=
  deepSATSearch_of_universalDynamicNFrameLagrangianExtraction
    S.U S.enc hextract
    (satDecisionReflection_of_surface S)

/-- Plugging a reflection surface into faithful PAC/holography live-minor
extraction closes deep SAT search for that machine model. -/
theorem deepSATSearch_of_faithfulDischarge_and_reflectionSurface
    (S : EncodedDTMDecisionReflectionSurface)
    (hdischarge : FaithfulPACHolographyLiveMinorDischarge S.enc) :
    DeepSATSearch S.U :=
  deepSATSearch_of_faithfulPACHolographyLiveMinorDischarge
    S.U S.enc hdischarge
    (satDecisionReflection_of_surface S)

/-! ## Axiom trace -/

#print axioms satDecisionReflection_of_surface
#print axioms deepSATSearch_of_dynamicExtraction_and_reflectionSurface
#print axioms deepSATSearch_of_faithfulDischarge_and_reflectionSurface

end PallLean.Paper93.DeepMath.PathB
