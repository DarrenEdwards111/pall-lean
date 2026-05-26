import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWilliamsMetacomplexityInvariant
import PallLean.Paper93.DeepMath.PathB.DynamicNFrameLagrangianExtractionEquivalence
import PallLean.Paper93.DeepMath.PathB.FaithfulLiveMinorObstruction

/-!
# Concrete PAC/Lagrangian → Williams invariant wiring

This file wires the paper's PAC/Lagrangian extraction objects into the
`WilliamsMetacomplexityInvariant` socket.

Because the PAC/Lagrangian side is formalized over the repository's DTM+encoding
surface, while `WilliamsMetacomplexityInvariant` is parameterized by an abstract
`MachineModel`, the bridge is made explicit as a hypothesis:

* `shallow_to_encoded_decider`: shallow SAT search in `U` yields an encoded DTM
  SAT decider witness.

Given that bridge, a PAC/Lagrangian no-decider theorem supplies the barrier.
-/

namespace PallLean.Paper93.DeepMath.PathB

open SATDepthMachine

/-- Bridge premise: SAT decision in `U` can be reflected into the repository's
encoded DTM SAT-decider surface. -/
def SATDecisionToEncodedDTMBridge
    (U : MachineModel)
    (enc : ThreeCNFEncoding) : Prop :=
  SATDecisionInP U ->
    (∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M)

/-- The explicit bridge hypothesis used by the Williams wiring follows from a
SAT-decision reflection bridge, via `decider_of_shallowSATSearch`. -/
theorem shallow_to_encoded_decider_of_satDecisionBridge
    (U : MachineModel)
    (enc : ThreeCNFEncoding)
    (hbridge : SATDecisionToEncodedDTMBridge U enc) :
    ShallowSATSearch U ->
      (∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) := by
  intro hshallow
  exact hbridge (decider_of_shallowSATSearch U hshallow)

/-- Build a Williams consequence carrying the encoded-DTM decider existence
predicate. -/
def encodedDeciderConsequence (enc : ThreeCNFEncoding) : WilliamsConsequence where
  payload := ∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M

/-- Universal dynamic N-frame/Lagrangian extraction yields a concrete
Williams/metacomplexity invariant, once the abstract-model-to-encoding bridge is
provided. -/
def williamsInvariant_of_universalDynamicNFrameLagrangianExtraction
    (U : MachineModel)
    (enc : ThreeCNFEncoding)
    (hextract : UniversalDynamicNFrameLagrangianExtraction enc)
    (shallow_to_encoded_decider :
      ShallowSATSearch U ->
        (∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M)) :
    WilliamsMetacomplexityInvariant U where
  consequence_of_shallow := fun _ => encodedDeciderConsequence enc
  barrier := by
    intro hshallow hc
    have hdec : ∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M := by
      simpa [encodedDeciderConsequence] using hc
    exact
      (no_DTMDecidesSATWithEncoding_of_universalDynamicNFrameLagrangianExtraction
        enc hextract) hdec
  consequence_sound := by
    intro hshallow
    exact shallow_to_encoded_decider hshallow

/-- Faithful PAC/holography live-minor discharge gives the same concrete
Williams invariant under the same explicit bridge hypothesis. -/
def williamsInvariant_of_faithfulPACHolographyLiveMinorDischarge
    (U : MachineModel)
    (enc : ThreeCNFEncoding)
    (hdischarge : FaithfulPACHolographyLiveMinorDischarge enc)
    (shallow_to_encoded_decider :
      ShallowSATSearch U ->
        (∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M)) :
    WilliamsMetacomplexityInvariant U where
  consequence_of_shallow := fun _ => encodedDeciderConsequence enc
  barrier := by
    intro hshallow hc
    have hdec : ∃ M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M := by
      simpa [encodedDeciderConsequence] using hc
    exact
      (no_DTMDecidesSATWithEncoding_of_FaithfulPACHolographyLiveMinorDischarge
        enc hdischarge) hdec
  consequence_sound := by
    intro hshallow
    exact shallow_to_encoded_decider hshallow

/-- Discharged version: only require SAT-decision reflection into encoded DTM
surfaces, not a separate shallow-search bridge. -/
def williamsInvariant_of_universalDynamicNFrameLagrangianExtraction_discharged
    (U : MachineModel)
    (enc : ThreeCNFEncoding)
    (hextract : UniversalDynamicNFrameLagrangianExtraction enc)
    (hbridge : SATDecisionToEncodedDTMBridge U enc) :
    WilliamsMetacomplexityInvariant U :=
  williamsInvariant_of_universalDynamicNFrameLagrangianExtraction
    U enc hextract
    (shallow_to_encoded_decider_of_satDecisionBridge U enc hbridge)

/-- Discharged version for the faithful PAC/holography live-minor route. -/
def williamsInvariant_of_faithfulPACHolographyLiveMinorDischarge_discharged
    (U : MachineModel)
    (enc : ThreeCNFEncoding)
    (hdischarge : FaithfulPACHolographyLiveMinorDischarge enc)
    (hbridge : SATDecisionToEncodedDTMBridge U enc) :
    WilliamsMetacomplexityInvariant U :=
  williamsInvariant_of_faithfulPACHolographyLiveMinorDischarge
    U enc hdischarge
    (shallow_to_encoded_decider_of_satDecisionBridge U enc hbridge)

/-! ## Axiom trace -/

#print axioms shallow_to_encoded_decider_of_satDecisionBridge
#print axioms williamsInvariant_of_universalDynamicNFrameLagrangianExtraction
#print axioms williamsInvariant_of_faithfulPACHolographyLiveMinorDischarge
#print axioms williamsInvariant_of_universalDynamicNFrameLagrangianExtraction_discharged
#print axioms williamsInvariant_of_faithfulPACHolographyLiveMinorDischarge_discharged

end PallLean.Paper93.DeepMath.PathB
