import PallLean.Paper93.DeepMath.PathB.DynamicNFrameLagrangianInvariant
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDegreeOrBoundaryStepA

/-!
# Global God-Move bridge to live boundary rank (paper-faithful quantifiers)

This module rewrites the bridge in the quantifier shape used by the `p vs np1`
paper: a universal extraction theorem over polynomial-time SAT observers,
parametrized by exponent and producing a large enough input length.

The old fixed-scale payload socket (`∀ L W, ...`) is stronger than what the
paper requires and obscures the true load-bearing theorem.  The corrected
bridge below makes that theorem explicit and leaves only one honest remaining
obligation.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Paper-faithful bridge statement: this is the real missing theorem.

Interpretation: for every polynomial width exponent `c`, there is a large enough
length `n` at which every DTM-backed SAT observer trajectory exposes a certified
live N-frame/Lagrangian minor with binomial lower bound.
-/
abbrev GlobalGodMovePaperBridge
    (enc : ThreeCNFEncoding) : Prop :=
  UniversalDynamicNFrameLagrangianExtraction enc

/-- Compatibility packaging with the corrected Step-A polarity.

`stepA_boundary_floor` is kept explicit for route-level auditing, while the
load-bearing SAT-side edge is exactly `globalGodMove_paperBridge`.
-/
structure GlobalGodMoveLiveBoundaryBridgeAssumptions
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop where
  stepA_boundary_floor : DegreeOrBoundaryExpansionFloorAtScale enc n
  globalGodMove_paperBridge : GlobalGodMovePaperBridge enc

/-- Fixed-scale extraction consequence from the paper-faithful bridge.

For any exponent `c`, extract the corresponding `n` and obtain a concrete live
minor for each dynamic SAT observer at that length.
-/
theorem dynamicExtractionAt_of_globalGodMovePaperBridge
    (enc : ThreeCNFEncoding)
    (H : GlobalGodMovePaperBridge enc)
    (c : Nat) :
    ∃ n : Nat,
      n >= 2 ^ 20 /\
      4 * (c + 1) <= Nat.log 2 n /\
      DynamicNFrameLagrangianExtractionAt enc n :=
  H c

/-- Bridge to the existing faithful-observer extraction socket.

This is the key wiring theorem showing the paper-faithful quantifier form is
already sufficient for the current infrastructure; no stronger `∀ L W` payload
builder is needed.
-/
theorem universalFaithfulExtraction_of_globalGodMovePaperBridge
    (enc : ThreeCNFEncoding)
    (H : GlobalGodMovePaperBridge enc) :
    UniversalFaithfulSATObserverGodMoveExtraction enc :=
  faithfulExtraction_of_dynamicNFrameLagrangianExtraction enc H

/-! ## Axiom trace -/

#print axioms dynamicExtractionAt_of_globalGodMovePaperBridge
#print axioms universalFaithfulExtraction_of_globalGodMovePaperBridge

end PallLean.Paper93.DeepMath.PathB
