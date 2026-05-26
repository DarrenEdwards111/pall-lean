import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWilliamsPACLagrangianBridge

/-!
# Williams/PAC final discharge wrappers

This file packages the two remaining obligations into explicit constructive
interfaces and derives end-to-end closure theorems from them.
-/

namespace PallLean.Paper93.DeepMath.PathB

open SATDepthMachine

/-- Constructive reflection interface from abstract SAT decision machines to the
repository's encoded DTM SAT-decider surface. -/
structure SATDecisionReflectionToEncodedDTM
    (U : MachineModel)
    (enc : ThreeCNFEncoding) where
  reflect : DecisionMachine U -> TuringMachine.DTM
  reflects_correct :
    ∀ D : DecisionMachine U,
      DecidesSAT U D -> DTMDecidesSATWithEncoding enc (reflect D)

/-- A constructive reflection interface discharges
`SATDecisionToEncodedDTMBridge`. -/
theorem satDecisionToEncodedDTMBridge_of_reflection
    (U : MachineModel)
    (enc : ThreeCNFEncoding)
    (R : SATDecisionReflectionToEncodedDTM U enc) :
    SATDecisionToEncodedDTMBridge U enc := by
  intro hdec
  rcases hdec with ⟨D, hD⟩
  exact ⟨R.reflect D, R.reflects_correct D hD⟩

/-- End-to-end: universal dynamic N-frame/Lagrangian extraction implies deep
SAT search once a constructive SAT-decision reflection exists. -/
theorem deepSATSearch_of_universalDynamicNFrameLagrangianExtraction
    (U : MachineModel)
    (enc : ThreeCNFEncoding)
    (hextract : UniversalDynamicNFrameLagrangianExtraction enc)
    (R : SATDecisionReflectionToEncodedDTM U enc) :
    DeepSATSearch U :=
  deepSATSearch_of_williamsInvariant U
    (williamsInvariant_of_universalDynamicNFrameLagrangianExtraction_discharged
      U enc hextract
      (satDecisionToEncodedDTMBridge_of_reflection U enc R))

/-- End-to-end: faithful PAC/holography live-minor discharge implies deep SAT
search once a constructive SAT-decision reflection exists. -/
theorem deepSATSearch_of_faithfulPACHolographyLiveMinorDischarge
    (U : MachineModel)
    (enc : ThreeCNFEncoding)
    (hdischarge : FaithfulPACHolographyLiveMinorDischarge enc)
    (R : SATDecisionReflectionToEncodedDTM U enc) :
    DeepSATSearch U :=
  deepSATSearch_of_williamsInvariant U
    (williamsInvariant_of_faithfulPACHolographyLiveMinorDischarge_discharged
      U enc hdischarge
      (satDecisionToEncodedDTMBridge_of_reflection U enc R))

/-! ## Axiom trace -/

#print axioms satDecisionToEncodedDTMBridge_of_reflection
#print axioms deepSATSearch_of_universalDynamicNFrameLagrangianExtraction
#print axioms deepSATSearch_of_faithfulPACHolographyLiveMinorDischarge

end PallLean.Paper93.DeepMath.PathB
