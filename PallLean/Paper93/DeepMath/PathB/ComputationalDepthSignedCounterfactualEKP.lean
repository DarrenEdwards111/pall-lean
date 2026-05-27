import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTriAspectSemanticInterface

/-!
# Signed counterfactual EKP surface

The existing `CounterfactualEKPDirectionCoverage` is intentionally tied to the
current `ThreeCNF` syntax.  That syntax is positive-only in this repository, and
`ComputationalDepthCounterfactualEKP` proves that it cannot supply genuine
SAT/UNSAT counterfactual pairs.

This file adds the missing signed/formula-parametric surface without deleting
the old audit.  It keeps the paper-instrumented Theorem-207 route separate from
the local Cook--Levin product-form bulk, and exposes the real remaining theorem
as a signed semantic transport into the paper-instrumented full/deleted
polynomials.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open PaperFaithfulSeparation
open InstrumentedSheetAudit

/-! ## Signed formula encoding -/

/-- A formula surface with signed satisfiability semantics.

Unlike the current positive-only `ThreeCNF`, this is allowed to contain
unsatisfiable formulas.  `Encodes` is length-indexed so the same semantic
surface can be used for counterfactual input pairs at different lengths. -/
structure SignedFormulaEncoding where
  Formula : Type
  Encodes : {n : Nat} -> (Fin n -> Bool) -> Formula -> Prop
  Satisfiable : Formula -> Prop

/-- A signed EKP direction label.  The label is intentionally lightweight; the
content is carried by the injective assignment of labels to SAT/UNSAT
intervention pairs. -/
structure SignedCounterfactualEKPDirection
    (_enc : SignedFormulaEncoding) (_n : Nat) where
  tag : Nat

/-- Signed counterfactual EKP coverage.

This is the replacement target for the positive-only coverage layer: the
negative side is genuinely unsatisfiable in the supplied formula semantics. -/
structure SignedCounterfactualEKPDirectionCoverage
    (enc : SignedFormulaEncoding) (M : DTM) (n : Nat) : Type where
  hn : n >= 1
  directionCount : Nat
  directionCount_pos : 0 < directionCount
  direction_floor :
    Nat.choose (n / 3) (Nat.log 2 n) <= directionCount
  positiveInput : Fin directionCount -> Fin n -> Bool
  negativeInput : Fin directionCount -> Fin n -> Bool
  positiveFormula : Fin directionCount -> enc.Formula
  negativeFormula : Fin directionCount -> enc.Formula
  positive_encoded :
    forall d : Fin directionCount,
      enc.Encodes (positiveInput d) (positiveFormula d)
  negative_encoded :
    forall d : Fin directionCount,
      enc.Encodes (negativeInput d) (negativeFormula d)
  positive_satisfiable :
    forall d : Fin directionCount,
      enc.Satisfiable (positiveFormula d)
  negative_unsatisfiable :
    forall d : Fin directionCount,
      Not (enc.Satisfiable (negativeFormula d))
  positive_accepts :
    forall d : Fin directionCount,
      TuringMachine.accepts M n hn (positiveInput d)
  negative_not_accepts :
    forall d : Fin directionCount,
      Not (TuringMachine.accepts M n hn (negativeInput d))
  directionOf :
    Fin directionCount -> SignedCounterfactualEKPDirection enc n
  direction_injective : Function.Injective directionOf

namespace SignedCounterfactualEKPDirectionCoverage

/-- A canonical first direction, available because the coverage object carries
`directionCount_pos`. -/
def first
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (C : SignedCounterfactualEKPDirectionCoverage enc M n) :
    Fin C.directionCount :=
  ⟨0, C.directionCount_pos⟩

end SignedCounterfactualEKPDirectionCoverage

/-! ## Signed run semantics -/

/-- Actual signed SAT run semantics extracted from signed counterfactual
coverage. -/
structure SignedActualSATRunSemantics
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    (C : SignedCounterfactualEKPDirectionCoverage enc M n) : Type where
  positive_satisfiable :
    forall d : Fin C.directionCount,
      enc.Satisfiable (C.positiveFormula d)
  negative_unsatisfiable :
    forall d : Fin C.directionCount,
      Not (enc.Satisfiable (C.negativeFormula d))
  positive_run_accepts :
    forall d : Fin C.directionCount,
      TuringMachine.accepts M n C.hn (C.positiveInput d)
  negative_run_rejects :
    forall d : Fin C.directionCount,
      Not (TuringMachine.accepts M n C.hn (C.negativeInput d))

namespace SignedActualSATRunSemantics

def ofCoverage
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    (C : SignedCounterfactualEKPDirectionCoverage enc M n) :
    SignedActualSATRunSemantics C where
  positive_satisfiable := C.positive_satisfiable
  negative_unsatisfiable := C.negative_unsatisfiable
  positive_run_accepts := C.positive_accepts
  negative_run_rejects := C.negative_not_accepts

end SignedActualSATRunSemantics

/-! ## Paper-instrumented semantics over signed coverage -/

/-- Paper-instrumented pair semantics over signed counterfactual coverage.

This mirrors the instrumented tri-aspect route but avoids the positive-only
`ThreeCNF` blocker.  It does not identify `W.paperCompiledPoly` with the local
Cook--Levin product-form bulk. -/
structure SignedPaperInstrumentedPairSemantics
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns)
    (C : SignedCounterfactualEKPDirectionCoverage enc M n)
    (A : SignedActualSATRunSemantics C) : Type where
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

namespace SignedPaperInstrumentedPairSemantics

/-- Signed paper-instrumented semantics gives Theorem-207 essentiality directly
for the canonical witness sheet. -/
theorem theorem207Essentiality
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns}
    {C : SignedCounterfactualEKPDirectionCoverage enc M n}
    (P :
      SignedPaperInstrumentedPairSemantics W C
        (SignedActualSATRunSemantics.ofCoverage C)) :
    Theorem207SheetEssentialForAcceptance
      (fun p => exists d : Fin C.directionCount, P.PairSeparates p d)
      (instrumentedSheet_of_theorem207Witness W) := by
  let d := C.first
  constructor
  · refine ⟨d, ?_⟩
    have hpos := (SignedActualSATRunSemantics.ofCoverage C).positive_run_accepts d
    have hneg := (SignedActualSATRunSemantics.ofCoverage C).negative_run_rejects d
    have hsepW : P.PairSeparates W.paperCompiledPoly d :=
      (P.paper_pair_exact d).2 ⟨hpos, hneg⟩
    simpa [instrumentedSheet_of_theorem207Witness,
      GlobalGodMoveGauge.theorem207Extraction_of_witness] using hsepW
  · intro hacc
    rcases hacc with ⟨e, hsep⟩
    exact P.sheet_loses_all_pairs e
      (by
        simpa [instrumentedSheet_of_theorem207Witness,
          GlobalGodMoveGauge.theorem207Extraction_of_witness] using hsep)

end SignedPaperInstrumentedPairSemantics

/-- Signed paper-instrumented tri-aspect interface.

The hard theorem is the transport field: actual signed SAT run semantics must
be interpreted by the paper-instrumented polynomial pair. -/
structure SignedPaperInstrumentedTriAspectSemanticInterface
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns)
    (C : SignedCounterfactualEKPDirectionCoverage enc M n) : Type where
  instrumented_semantics_transport :
    forall A : SignedActualSATRunSemantics C,
      SignedPaperInstrumentedPairSemantics W C A

namespace SignedPaperInstrumentedTriAspectSemanticInterface

def toSignedPaperInstrumentedPairSemantics
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns}
    {C : SignedCounterfactualEKPDirectionCoverage enc M n}
    (I : SignedPaperInstrumentedTriAspectSemanticInterface W C) :
    SignedPaperInstrumentedPairSemantics W C
      (SignedActualSATRunSemantics.ofCoverage C) :=
  I.instrumented_semantics_transport (SignedActualSATRunSemantics.ofCoverage C)

theorem theorem207Essentiality
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns}
    {C : SignedCounterfactualEKPDirectionCoverage enc M n}
    (I : SignedPaperInstrumentedTriAspectSemanticInterface W C) :
    Theorem207SheetEssentialForAcceptance
      (fun p => exists d : Fin C.directionCount,
        (toSignedPaperInstrumentedPairSemantics I).PairSeparates p d)
      (instrumentedSheet_of_theorem207Witness W) :=
  (toSignedPaperInstrumentedPairSemantics I).theorem207Essentiality

end SignedPaperInstrumentedTriAspectSemanticInterface

/-- Canonical signed paper-instrumented bridge: every canonical witness and
signed coverage family has a paper-instrumented semantic transport. -/
structure CanonicalSignedPaperInstrumentedTriAspectBridge
    (enc : SignedFormulaEncoding) : Type where
  interface :
    forall {M : DTM} {n : Nat}
      {hn : n >= 2 ^ 804} {hn2 : n >= 2}
      {htb : M.timeBound <= 4} {hns : M.numStates <= n}
      (W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns)
      (C : SignedCounterfactualEKPDirectionCoverage enc M n),
        Nonempty (SignedPaperInstrumentedTriAspectSemanticInterface W C)

/-- The signed canonical bridge yields ordinary Theorem-207 essentiality for
the canonical sheet. -/
theorem theorem207Essentiality_of_canonicalSignedPaperInstrumentedBridge
    (enc : SignedFormulaEncoding)
    (H : CanonicalSignedPaperInstrumentedTriAspectBridge enc)
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns)
    (C : SignedCounterfactualEKPDirectionCoverage enc M n) :
    Exists (fun Accepts =>
      Theorem207SheetEssentialForAcceptance Accepts
        (instrumentedSheet_of_theorem207Witness W)) := by
  rcases H.interface W C with ⟨I⟩
  exact ⟨
    (fun p => exists d : Fin C.directionCount,
      (I.toSignedPaperInstrumentedPairSemantics).PairSeparates p d),
    I.theorem207Essentiality
  ⟩

/-! ## Kernel-only axiom trace -/

#print axioms SignedActualSATRunSemantics.ofCoverage
#print axioms SignedPaperInstrumentedPairSemantics.theorem207Essentiality
#print axioms SignedPaperInstrumentedTriAspectSemanticInterface.toSignedPaperInstrumentedPairSemantics
#print axioms SignedPaperInstrumentedTriAspectSemanticInterface.theorem207Essentiality
#print axioms theorem207Essentiality_of_canonicalSignedPaperInstrumentedBridge

end PallLean.Paper93.DeepMath.PathB
