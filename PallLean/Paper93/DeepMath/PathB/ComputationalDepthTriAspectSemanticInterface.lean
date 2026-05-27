import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGroundedCookLevinObstruction

/-!
# Tri-aspect semantic interface (split grounded vs instrumented)

This file splits the tri-aspect surface into:

1. `GroundedTriAspectSemanticInterface`: tied to the local Cook--Levin bulk
   via `HolographicProjectionSemanticInterface`.
2. `InstrumentedTriAspectSemanticInterface`: paper-instrumented route with an
   explicit transport field from signed-run semantics, without identifying the
   paper object with `actualCookLevinBulkPoly`.

The split avoids conflating the grounded obstruction with the paper-level
instrumented bridge target.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open PaperFaithfulSeparation
open InstrumentedSheetAudit

/-! ## Grounded split -/

structure GroundedTriAspectSemanticInterface
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns)
    (C : CounterfactualEKPDirectionCoverage enc M n)
    : Type
    extends HolographicProjectionSemanticInterface S C where
  bulk_pair_exact :
    forall d : Fin C.directionCount,
      PairSeparates S.extraction.paperCompiledPoly d <->
        (TuringMachine.accepts M n C.hn (C.positiveInput d) /\
         Not (TuringMachine.accepts M n C.hn (C.negativeInput d)))

structure GroundedTriAspectSemanticBridge
    (enc : ThreeCNFEncoding) : Type where
  interface :
    forall {M : DTM} {n : Nat}
      {hn : n >= 2 ^ 804} {hn2 : n >= 2}
      {htb : M.timeBound <= 4} {hns : M.numStates <= n}
      (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns)
      (C : CounterfactualEKPDirectionCoverage enc M n),
        Nonempty (GroundedTriAspectSemanticInterface S C)

/-- Grounded route still implies the existing counterfactual binding bridge. -/
def counterfactualBridge_of_groundedTriAspectSemanticBridge
    (enc : ThreeCNFEncoding)
    (H : GroundedTriAspectSemanticBridge enc) :
    CounterfactualEKPToTheorem207Essentiality enc where
  bind := by
    intro M n hn hn2 htb hns S C
    rcases H.interface S C with ⟨I⟩
    exact ⟨I.toSheetBindsCounterfactualSwitches⟩

/-- Grounded interface yields ordinary Theorem-207 essentiality. -/
theorem theorem207Essentiality_of_groundedTriAspectInterface
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {S : InstrumentedTheorem207Sheet M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    (I : GroundedTriAspectSemanticInterface S C) :
    Theorem207SheetEssentialForAcceptance
      (I.toActualPairPolynomialSemantics).Accepts S :=
  I.theorem207Essentiality_of_holographicProjectionInterface

/-! ## Instrumented split -/

/-- Placeholder for signed-CNF run semantics (separate from positive-only
`ThreeCNF` local semantics). -/
structure ActualSignedSATRunSemantics
    (enc : ThreeCNFEncoding) (M : DTM) (n : Nat) : Type where
  witness : Prop

/-- Paper-instrumented pair semantics for a canonical Theorem-207 witness. -/
structure PaperInstrumentedPairSemantics
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns)
    {enc : ThreeCNFEncoding}
    (C : CounterfactualEKPDirectionCoverage enc M n) : Type where
  PairSeparates : Fin C.directionCount -> Prop

/-- Paper-instrumented tri-aspect interface.

No grounding equation to `actualCookLevinBulkPoly` is included here. -/
structure InstrumentedTriAspectSemanticInterface
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns)
    (C : CounterfactualEKPDirectionCoverage enc M n) : Type where
  instrumented_semantics_transport :
    ActualSignedSATRunSemantics enc M n ->
      PaperInstrumentedPairSemantics W C

structure CanonicalTriAspectSemanticBridge
    (enc : ThreeCNFEncoding) : Type where
  interface :
    forall {M : DTM} {n : Nat}
      {hn : n >= 2 ^ 804} {hn2 : n >= 2}
      {htb : M.timeBound <= 4} {hns : M.numStates <= n}
      (W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns)
      (C : CounterfactualEKPDirectionCoverage enc M n),
        Nonempty (InstrumentedTriAspectSemanticInterface W C)

/-! ## Shared obstruction marker -/

/-- Grounded Cook--Levin obstruction remains unchanged for legacy witnesses. -/
theorem no_legacy_grounding_to_actualCookLevinBulk
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (W : GlobalGodMoveGauge.Theorem207Witness
      M n hn (by omega : n >= 2) htb hns) :
    Not (W.paperCompiledPoly =
      actualCookLevinBulkPoly M n (by omega : n >= 2) htb hns) :=
  no_theorem207Witness_grounded_to_actualCookLevinBulk M n hn htb hns W

/-! ## Kernel-only axiom trace -/

#print axioms counterfactualBridge_of_groundedTriAspectSemanticBridge
#print axioms theorem207Essentiality_of_groundedTriAspectInterface
#print axioms no_legacy_grounding_to_actualCookLevinBulk

end PallLean.Paper93.DeepMath.PathB
