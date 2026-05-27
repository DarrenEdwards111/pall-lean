import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGroundedCookLevinObstruction

/-!
# Tri-aspect semantic interface (Book-1 style surface)

This file encodes a minimal, checkable "tri-aspect" surface where one object
is linked across three views:

1. computational view: actual DTM accept/not-accept behavior on intervention pairs;
2. boundary view: holographic projected sheet semantics;
3. interventional view: counterfactual EKP direction-indexed pair family.

It is a wiring layer only.  It does not claim the hard existence theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open PaperFaithfulSeparation
open InstrumentedSheetAudit

/-- A tri-aspect refinement of the holographic semantic interface.

The extra field `bulk_pair_exact` enforces exact semantic transport at the
bulk polynomial for each intervention pair, not just one-way implication. -/
structure TriAspectSemanticInterface
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

/-- Global tri-aspect linchpin target.

This is the Book-1 compatibility shape made precise: for every relevant
instrumented sheet and intervention family, produce a tri-aspect interface. -/
structure TriAspectSemanticBridge
    (enc : ThreeCNFEncoding) : Type where
  interface :
    forall {M : DTM} {n : Nat}
      {hn : n >= 2 ^ 804} {hn2 : n >= 2}
      {htb : M.timeBound <= 4} {hns : M.numStates <= n}
      (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns)
      (C : CounterfactualEKPDirectionCoverage enc M n),
        Nonempty (TriAspectSemanticInterface S C)

/-- Any tri-aspect bridge gives the previously defined counterfactual
essentiality bridge (forgetting the exactness field). -/
def counterfactualBridge_of_triAspectSemanticBridge
    (enc : ThreeCNFEncoding)
    (H : TriAspectSemanticBridge enc) :
    CounterfactualEKPToTheorem207Essentiality enc where
  bind := by
    intro M n hn hn2 htb hns S C
    rcases H.interface S C with ⟨I⟩
    exact ⟨I.toSheetBindsCounterfactualSwitches⟩

/-- A tri-aspect interface still enforces ordinary Theorem-207 essentiality. -/
theorem theorem207Essentiality_of_triAspectInterface
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {S : InstrumentedTheorem207Sheet M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    (I : TriAspectSemanticInterface S C) :
    Theorem207SheetEssentialForAcceptance
      (I.toActualPairPolynomialSemantics).Accepts S :=
  I.theorem207Essentiality_of_holographicProjectionInterface

/-- Grounded Cook--Levin obstruction remains: legacy Theorem-207 witnesses
cannot be grounded to the actual Cook--Levin bulk object. -/
theorem no_legacy_grounding_to_actualCookLevinBulk
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (W : GlobalGodMoveGauge.Theorem207Witness
      M n hn (by omega : n >= 2) htb hns) :
    Not (W.paperCompiledPoly =
      actualCookLevinBulkPoly M n (by omega : n >= 2) htb hns) :=
  no_theorem207Witness_grounded_to_actualCookLevinBulk M n hn htb hns W

/-! ## Kernel-only axiom trace -/

#print axioms counterfactualBridge_of_triAspectSemanticBridge
#print axioms theorem207Essentiality_of_triAspectInterface
#print axioms no_legacy_grounding_to_actualCookLevinBulk

end PallLean.Paper93.DeepMath.PathB
