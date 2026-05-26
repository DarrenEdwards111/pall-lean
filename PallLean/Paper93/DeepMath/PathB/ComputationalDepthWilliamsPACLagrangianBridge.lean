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

/-! ## Axiom trace -/

#print axioms williamsInvariant_of_universalDynamicNFrameLagrangianExtraction
#print axioms williamsInvariant_of_faithfulPACHolographyLiveMinorDischarge

end PallLean.Paper93.DeepMath.PathB
