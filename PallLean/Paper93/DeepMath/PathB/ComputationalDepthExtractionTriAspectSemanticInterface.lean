import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSignedThreeCNFModel

/-!
# Extraction-level tri-aspect semantic interface

The full `Theorem207Witness` bundles more than semantic extraction: it also
carries the P-side upper bound and the NP-side lower bound that form the
paper-scale contradiction.  This file factors the semantic-transport layer
through the weaker `InstrumentedTheorem207Sheet` surface instead.

That is the cleaner target:

* signed counterfactual SAT/UNSAT coverage supplies actual intervention facts;
* an extraction-level paper-instrumented semantic transport interprets those
  facts through the extracted full/deleted polynomial pair;
* this alone yields sheet essentiality.

No grounding equation to the local Cook--Levin product-form bulk is used, and
no P-side rank upper bound is assumed in the semantic transport step.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open PaperFaithfulSeparation
open InstrumentedSheetAudit

/-! ## Extraction-level signed pair semantics -/

/-- Paper-instrumented pair semantics over a raw instrumented extraction
surface, not a full contradiction-bearing `Theorem207Witness`.

This is the semantic transport theorem's local target.  The field
`paper_pair_exact` ties the paper-compiled polynomial to actual signed
accept/reject intervention pairs, while `sheet_loses_all_pairs` says the
extracted sheet alone does not carry those pair separations. -/
structure SignedExtractionInstrumentedPairSemantics
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns)
    (C : SignedCounterfactualEKPDirectionCoverage enc M n)
    (_A : SignedActualSATRunSemantics C) : Type where
  PairSeparates :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ ->
      Fin C.directionCount -> Prop
  paper_pair_exact :
    forall d : Fin C.directionCount,
      PairSeparates S.extraction.paperCompiledPoly d <->
        (TuringMachine.accepts M n C.hn (C.positiveInput d) /\
          Not (TuringMachine.accepts M n C.hn (C.negativeInput d)))
  sheet_loses_all_pairs :
    forall d : Fin C.directionCount,
      Not (PairSeparates S.extraction.coupledSheet d)
  sheetDirection : Fin C.directionCount -> Nat
  sheetDirection_injective : Function.Injective sheetDirection

namespace SignedExtractionInstrumentedPairSemantics

/-- Extraction-level signed pair semantics yields ordinary Theorem-207 sheet
essentiality.  This is the local semantic-transport wiring theorem, proved
without a full `Theorem207Witness` and without any P-side rank upper bound. -/
theorem theorem207Essentiality
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {S : InstrumentedTheorem207Sheet M n hn hn2 htb hns}
    {C : SignedCounterfactualEKPDirectionCoverage enc M n}
    (P :
      SignedExtractionInstrumentedPairSemantics S C
        (SignedActualSATRunSemantics.ofCoverage C)) :
    Theorem207SheetEssentialForAcceptance
      (fun p => exists d : Fin C.directionCount, P.PairSeparates p d)
      S := by
  let d := C.first
  constructor
  · refine ⟨d, ?_⟩
    have hpos := (SignedActualSATRunSemantics.ofCoverage C).positive_run_accepts d
    have hneg := (SignedActualSATRunSemantics.ofCoverage C).negative_run_rejects d
    exact (P.paper_pair_exact d).2 ⟨hpos, hneg⟩
  · intro hacc
    rcases hacc with ⟨e, hsep⟩
    exact P.sheet_loses_all_pairs e hsep

end SignedExtractionInstrumentedPairSemantics

/-! ## Extraction-level tri-aspect interface -/

/-- Extraction-level tri-aspect semantic interface.

The single hard field is the semantic transport from actual signed SAT run
facts into the paper-instrumented extraction pair.  This is the version that
does not inherit the full `Theorem207Witness` rank sandwich. -/
structure SignedExtractionTriAspectSemanticInterface
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns)
    (C : SignedCounterfactualEKPDirectionCoverage enc M n) : Type where
  instrumented_semantics_transport :
    forall A : SignedActualSATRunSemantics C,
      SignedExtractionInstrumentedPairSemantics S C A

namespace SignedExtractionTriAspectSemanticInterface

def toSignedExtractionInstrumentedPairSemantics
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {S : InstrumentedTheorem207Sheet M n hn hn2 htb hns}
    {C : SignedCounterfactualEKPDirectionCoverage enc M n}
    (I : SignedExtractionTriAspectSemanticInterface S C) :
    SignedExtractionInstrumentedPairSemantics S C
      (SignedActualSATRunSemantics.ofCoverage C) :=
  I.instrumented_semantics_transport (SignedActualSATRunSemantics.ofCoverage C)

theorem theorem207Essentiality
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {S : InstrumentedTheorem207Sheet M n hn hn2 htb hns}
    {C : SignedCounterfactualEKPDirectionCoverage enc M n}
    (I : SignedExtractionTriAspectSemanticInterface S C) :
    Theorem207SheetEssentialForAcceptance
      (fun p => exists d : Fin C.directionCount,
        (toSignedExtractionInstrumentedPairSemantics I).PairSeparates p d)
      S :=
  (toSignedExtractionInstrumentedPairSemantics I).theorem207Essentiality

end SignedExtractionTriAspectSemanticInterface

/-! ## Canonical extraction bridge target -/

/-- Canonical signed extraction bridge.

This is the narrowed global semantic transport theorem: every canonical
instrumented extraction and signed counterfactual coverage family admits an
extraction-level tri-aspect interpretation.  It is deliberately stated over
`InstrumentedTheorem207Sheet`, not full `Theorem207Witness`. -/
structure CanonicalSignedExtractionTriAspectBridge
    (enc : SignedFormulaEncoding) : Type where
  interface :
    forall {M : DTM} {n : Nat}
      {hn : n >= 2 ^ 804} {hn2 : n >= 2}
      {htb : M.timeBound <= 4} {hns : M.numStates <= n}
      (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns)
      (C : SignedCounterfactualEKPDirectionCoverage enc M n),
        Nonempty (SignedExtractionTriAspectSemanticInterface S C)

/-- The extraction bridge gives ordinary sheet essentiality for any
instrumented extraction surface. -/
theorem theorem207Essentiality_of_canonicalSignedExtractionBridge
    (enc : SignedFormulaEncoding)
    (H : CanonicalSignedExtractionTriAspectBridge enc)
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns)
    (C : SignedCounterfactualEKPDirectionCoverage enc M n) :
    Exists (fun Accepts =>
      Theorem207SheetEssentialForAcceptance Accepts S) := by
  rcases H.interface S C with ⟨I⟩
  exact ⟨
    (fun p => exists d : Fin C.directionCount,
      (I.toSignedExtractionInstrumentedPairSemantics).PairSeparates p d),
    I.theorem207Essentiality
  ⟩

/-- A witness-level signed bridge can be weakened to the extraction-level
endpoint for the sheet induced by that witness.  This theorem is only a
compatibility check; the serious target is
`CanonicalSignedExtractionTriAspectBridge`, which avoids full witnesses. -/
theorem theorem207Essentiality_of_canonicalSignedExtractionBridge_forWitness
    (enc : SignedFormulaEncoding)
    (H : CanonicalSignedExtractionTriAspectBridge enc)
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns)
    (C : SignedCounterfactualEKPDirectionCoverage enc M n) :
    Exists (fun Accepts =>
      Theorem207SheetEssentialForAcceptance Accepts
        (instrumentedSheet_of_theorem207Witness W)) :=
  theorem207Essentiality_of_canonicalSignedExtractionBridge
    enc H (instrumentedSheet_of_theorem207Witness W) C

/-! ## Concrete signed model marker -/

/-- The concrete signed 3-CNF semantics removes the positive-only vacuity:
there are encoded satisfiable and encoded unsatisfiable formulas.  Transport
over this encoding is therefore not blocked by the old `ThreeCNF` syntax. -/
theorem signedThreeCNFEncoding_has_encoded_sat_and_unsat :
    (exists (n : Nat) (input : Fin n -> Bool)
        (φ : signedThreeCNFEncoding.Formula),
      signedThreeCNFEncoding.Encodes (n := n) input φ /\
      signedThreeCNFEncoding.Satisfiable φ) /\
    (exists (n : Nat) (input : Fin n -> Bool)
        (ψ : signedThreeCNFEncoding.Formula),
      signedThreeCNFEncoding.Encodes (n := n) input ψ /\
      Not (signedThreeCNFEncoding.Satisfiable ψ)) :=
  signedThreeCNFEncoding_encoded_nonvacuous

/-! ## Kernel-only axiom trace -/

#print axioms SignedExtractionInstrumentedPairSemantics.theorem207Essentiality
#print axioms SignedExtractionTriAspectSemanticInterface.toSignedExtractionInstrumentedPairSemantics
#print axioms SignedExtractionTriAspectSemanticInterface.theorem207Essentiality
#print axioms theorem207Essentiality_of_canonicalSignedExtractionBridge
#print axioms theorem207Essentiality_of_canonicalSignedExtractionBridge_forWitness
#print axioms signedThreeCNFEncoding_has_encoded_sat_and_unsat

end PallLean.Paper93.DeepMath.PathB
