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

/-- Actual signed SAT run semantics for a counterfactual intervention family.

This is the computational/interventional view.  It is kept separate from the
paper polynomial semantics.  In the current repository the existing
positive-only `ThreeCNF` surface prevents inhabiting nontrivial coverage; a
real instantiation of this surface should come from the signed-CNF layer. -/
structure ActualSignedSATRunSemantics
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    (C : CounterfactualEKPDirectionCoverage enc M n) : Type where
  positive_satisfiable :
    forall d : Fin C.directionCount,
      (C.positiveFormula d).IsSatisfiable
  negative_unsatisfiable :
    forall d : Fin C.directionCount,
      Not (C.negativeFormula d).IsSatisfiable
  positive_run_accepts :
    forall d : Fin C.directionCount,
      TuringMachine.accepts M n C.hn (C.positiveInput d)
  negative_run_rejects :
    forall d : Fin C.directionCount,
      Not (TuringMachine.accepts M n C.hn (C.negativeInput d))

namespace ActualSignedSATRunSemantics

/-- The actual signed-run semantics already carried by a counterfactual
coverage object. -/
def ofCoverage
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    (C : CounterfactualEKPDirectionCoverage enc M n) :
    ActualSignedSATRunSemantics C where
  positive_satisfiable := C.positive_satisfiable
  negative_unsatisfiable := C.negative_unsatisfiable
  positive_run_accepts := C.positive_accepts
  negative_run_rejects := C.negative_not_accepts

end ActualSignedSATRunSemantics

/-- Paper-instrumented pair semantics for a canonical Theorem-207 witness.

This is the boundary/paper view.  It deliberately does not assert that
`W.paperCompiledPoly` is the local Cook--Levin product-form bulk.  Instead it
records how actual signed SAT run facts are transported into the separate
paper-instrumented full/deleted polynomial pair. -/
structure PaperInstrumentedPairSemantics
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns)
    (C : CounterfactualEKPDirectionCoverage enc M n)
    (A : ActualSignedSATRunSemantics C) : Type where
  PairSeparates :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ ->
      Fin C.directionCount -> Prop
  paper_pair_exact :
    forall d : Fin C.directionCount,
      PairSeparates W.paperCompiledPoly d <->
        (TuringMachine.accepts M n C.hn (C.positiveInput d) /\
          Not (TuringMachine.accepts M n C.hn (C.negativeInput d)))
  sheet_loses_all_pairs :
    forall d : Fin C.directionCount,
      Not (PairSeparates W.sheet d)
  sheetDirection : Fin C.directionCount -> Nat
  sheetDirection_injective : Function.Injective sheetDirection

namespace PaperInstrumentedPairSemantics

/-- Paper-instrumented pair semantics supplies the existing actual-pair
polynomial semantics socket without grounding `paperCompiledPoly` as the local
Cook--Levin bulk. -/
def toActualPairPolynomialSemantics
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    (P :
      PaperInstrumentedPairSemantics W C
        (ActualSignedSATRunSemantics.ofCoverage C)) :
    ActualPairPolynomialSemantics
      (S := instrumentedSheet_of_theorem207Witness W)
      (ActualCounterfactualPairFacts.ofCoverage C) where
  Accepts := fun p => exists d : Fin C.directionCount, P.PairSeparates p d
  full_poly_accepts_of_pair := by
    intro d hpos
    refine ⟨d, ?_⟩
    have hneg := (ActualSignedSATRunSemantics.ofCoverage C).negative_run_rejects d
    have hsepW : P.PairSeparates W.paperCompiledPoly d :=
      (P.paper_pair_exact d).2 ⟨hpos, hneg⟩
    simpa [instrumentedSheet_of_theorem207Witness,
      GlobalGodMoveGauge.theorem207Extraction_of_witness] using hsepW
  deleted_poly_rejects_of_pair := by
    intro _d _hneg hacc
    rcases hacc with ⟨e, hsep⟩
    exact P.sheet_loses_all_pairs e
      (by
        simpa [instrumentedSheet_of_theorem207Witness,
          GlobalGodMoveGauge.theorem207Extraction_of_witness] using hsep)
  sheetDirection := P.sheetDirection
  sheetDirection_injective := P.sheetDirection_injective

/-- Paper-instrumented semantics binds counterfactual switches for the
canonical sheet generated by the witness. -/
noncomputable def toSheetBindsCounterfactualSwitches
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    (P :
      PaperInstrumentedPairSemantics W C
        (ActualSignedSATRunSemantics.ofCoverage C)) :
    SheetBindsCounterfactualSwitches
      (instrumentedSheet_of_theorem207Witness W) C :=
  SheetBindsCounterfactualSwitches.ofCoveragePolynomialSemantics
    (toActualPairPolynomialSemantics P)

theorem theorem207Essentiality
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    (P :
      PaperInstrumentedPairSemantics W C
        (ActualSignedSATRunSemantics.ofCoverage C)) :
    Theorem207SheetEssentialForAcceptance
      (toActualPairPolynomialSemantics P).Accepts
      (instrumentedSheet_of_theorem207Witness W) :=
  theorem207SheetEssentialForAcceptance_of_actualPairPolynomialSemantics
    (toActualPairPolynomialSemantics P)

end PaperInstrumentedPairSemantics

/-- Paper-instrumented tri-aspect interface.

No grounding equation to `actualCookLevinBulkPoly` is included here.  The hard
field is semantic transport from actual signed SAT runs into the paper-level
instrumented polynomial pair. -/
structure PaperInstrumentedTriAspectSemanticInterface
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns)
    (C : CounterfactualEKPDirectionCoverage enc M n) : Type where
  instrumented_semantics_transport :
    forall A : ActualSignedSATRunSemantics C,
      PaperInstrumentedPairSemantics W C A

namespace PaperInstrumentedTriAspectSemanticInterface

def toPaperInstrumentedPairSemantics
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    (I : PaperInstrumentedTriAspectSemanticInterface W C) :
    PaperInstrumentedPairSemantics W C
      (ActualSignedSATRunSemantics.ofCoverage C) :=
  I.instrumented_semantics_transport (ActualSignedSATRunSemantics.ofCoverage C)

noncomputable def toSheetBindsCounterfactualSwitches
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    (I : PaperInstrumentedTriAspectSemanticInterface W C) :
    SheetBindsCounterfactualSwitches
      (instrumentedSheet_of_theorem207Witness W) C :=
  (toPaperInstrumentedPairSemantics I).toSheetBindsCounterfactualSwitches

theorem theorem207Essentiality
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    (I : PaperInstrumentedTriAspectSemanticInterface W C) :
    Theorem207SheetEssentialForAcceptance
      ((toPaperInstrumentedPairSemantics I).toActualPairPolynomialSemantics).Accepts
      (instrumentedSheet_of_theorem207Witness W) :=
  (toPaperInstrumentedPairSemantics I).theorem207Essentiality

end PaperInstrumentedTriAspectSemanticInterface

/-- Canonical paper-instrumented tri-aspect bridge.

This is the serious paper-faithful target after the split: only canonical
Theorem-207 witnesses are in scope, and the paper polynomial stays separate
from the local Cook--Levin product-form bulk. -/
structure CanonicalPaperInstrumentedTriAspectSemanticBridge
    (enc : ThreeCNFEncoding) : Type where
  interface :
    forall {M : DTM} {n : Nat}
      {hn : n >= 2 ^ 804} {hn2 : n >= 2}
      {htb : M.timeBound <= 4} {hns : M.numStates <= n}
      (W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns)
      (C : CounterfactualEKPDirectionCoverage enc M n),
        Nonempty (PaperInstrumentedTriAspectSemanticInterface W C)

/-- The canonical paper-instrumented bridge recovers counterfactual binding for
canonical Theorem-207 sheets only. -/
def canonicalPaperInstrumentedCounterfactualBinding
    (enc : ThreeCNFEncoding)
    (H : CanonicalPaperInstrumentedTriAspectSemanticBridge enc)
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns)
    (C : CounterfactualEKPDirectionCoverage enc M n) :
    Nonempty
      (SheetBindsCounterfactualSwitches
        (instrumentedSheet_of_theorem207Witness W) C) := by
  rcases H.interface W C with ⟨I⟩
  exact ⟨I.toSheetBindsCounterfactualSwitches⟩

/-- The canonical paper-instrumented bridge gives ordinary Theorem-207
essentiality for the canonical sheet, without grounding `paperCompiledPoly` in
the local Cook--Levin bulk. -/
theorem theorem207Essentiality_of_canonicalPaperInstrumentedTriAspectBridge
    (enc : ThreeCNFEncoding)
    (H : CanonicalPaperInstrumentedTriAspectSemanticBridge enc)
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns)
    (C : CounterfactualEKPDirectionCoverage enc M n) :
    Exists (fun Accepts =>
      Theorem207SheetEssentialForAcceptance Accepts
        (instrumentedSheet_of_theorem207Witness W)) := by
  rcases H.interface W C with ⟨I⟩
  exact ⟨
    ((I.toPaperInstrumentedPairSemantics).toActualPairPolynomialSemantics).Accepts,
    I.theorem207Essentiality
  ⟩

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
#print axioms ActualSignedSATRunSemantics.ofCoverage
#print axioms PaperInstrumentedPairSemantics.toActualPairPolynomialSemantics
#print axioms PaperInstrumentedPairSemantics.toSheetBindsCounterfactualSwitches
#print axioms PaperInstrumentedPairSemantics.theorem207Essentiality
#print axioms PaperInstrumentedTriAspectSemanticInterface.toPaperInstrumentedPairSemantics
#print axioms PaperInstrumentedTriAspectSemanticInterface.toSheetBindsCounterfactualSwitches
#print axioms PaperInstrumentedTriAspectSemanticInterface.theorem207Essentiality
#print axioms canonicalPaperInstrumentedCounterfactualBinding
#print axioms theorem207Essentiality_of_canonicalPaperInstrumentedTriAspectBridge
#print axioms no_legacy_grounding_to_actualCookLevinBulk

end PallLean.Paper93.DeepMath.PathB
