import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExtractionTriAspectSemanticInterface

/-!
# Remainder-sensitive tri-aspect semantic interface

The extraction-level interface in
`ComputationalDepthExtractionTriAspectSemanticInterface` records:

* the full paper object separates signed SAT/UNSAT intervention pairs;
* the extracted sheet alone loses those separations.

That is not the right polarity for semantic force.  If the sheet is the
high-dimensional component, the meaningful deletion theorem is:

* the full paper object separates the intervention pairs;
* the remainder obtained after deleting the sheet loses those separations.

This file adds that remainder-sensitive surface.  It does not prove the
transport theorem; it states the sharper target and proves the local wiring
from such transport to sheet-essential-after-deletion.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open PaperFaithfulSeparation

/-! ## Extraction with explicit deleted-sheet remainder -/

/-- The polynomial space attached to the Cook--Levin compilation for `M,n`. -/
abbrev Theorem207PolySpace
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :=
  MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ

/-- Theorem-207 extraction with an explicit remainder/deleted-sheet object.

The equation

`paperCompiledPoly = coupledSheet + remainder`

is the formal version of the paper-level split
`P_{M,n}(u,v) = Q ×_Φ(u,ζ(u,v)) + R_{M,Φ}(v)`.
-/
structure Theorem207ExtractionWithRemainder
    (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Type where
  paperCompiledPoly :
    Theorem207PolySpace M n hn2 htb hns
  coupledSheet :
    Theorem207PolySpace M n hn2 htb hns
  remainder :
    Theorem207PolySpace M n hn2 htb hns
  full_eq_sheet_add_remainder :
    paperCompiledPoly = coupledSheet + remainder

namespace Theorem207ExtractionWithRemainder

/-- Forget the explicit remainder and recover the ordinary extraction surface.
-/
def toExtraction
    {M : DTM} {n : Nat} {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (E : Theorem207ExtractionWithRemainder M n hn hn2 htb hns) :
    GlobalGodMoveGauge.Theorem207Extraction M n hn hn2 htb hns where
  paperCompiledPoly := E.paperCompiledPoly
  coupledSheet := E.coupledSheet

end Theorem207ExtractionWithRemainder

/-- Remainder-sensitive sheet essentiality: the full paper object is accepted
while the deleted-sheet remainder is not. -/
def Theorem207SheetEssentialAfterDeletion
    {M : DTM} {n : Nat} {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (Accepts : Theorem207PolySpace M n hn2 htb hns -> Prop)
    (E : Theorem207ExtractionWithRemainder M n hn hn2 htb hns) : Prop :=
  Accepts E.paperCompiledPoly /\ Not (Accepts E.remainder)

/-! ## Remainder-sensitive signed pair semantics -/

/-- Remainder-sensitive paper-instrumented pair semantics.

The sheet is not required to lose pairs.  Instead, deleting the sheet and
keeping only the remainder loses all counterfactual SAT/UNSAT separations.
This is the polarity needed for a genuine "sheet is necessary" theorem. -/
structure SignedExtractionRemainderPairSemantics
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (E : Theorem207ExtractionWithRemainder M n hn hn2 htb hns)
    (C : SignedCounterfactualEKPDirectionCoverage enc M n)
    (_A : SignedActualSATRunSemantics C) : Type where
  PairSeparates :
    Theorem207PolySpace M n hn2 htb hns ->
      Fin C.directionCount -> Prop
  full_pair_exact :
    forall d : Fin C.directionCount,
      PairSeparates E.paperCompiledPoly d <->
        (TuringMachine.accepts M n C.hn (C.positiveInput d) /\
          Not (TuringMachine.accepts M n C.hn (C.negativeInput d)))
  remainder_loses_all_pairs :
    forall d : Fin C.directionCount,
      Not (PairSeparates E.remainder d)
  sheetDirection : Fin C.directionCount -> Nat
  sheetDirection_injective : Function.Injective sheetDirection

namespace SignedExtractionRemainderPairSemantics

/-- Remainder-sensitive semantics yields the intended deletion essentiality:
the full object separates at least one actual SAT/UNSAT intervention pair, but
the deleted-sheet remainder separates none. -/
theorem sheetEssentialityAfterDeletion
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {E : Theorem207ExtractionWithRemainder M n hn hn2 htb hns}
    {C : SignedCounterfactualEKPDirectionCoverage enc M n}
    (P :
      SignedExtractionRemainderPairSemantics E C
        (SignedActualSATRunSemantics.ofCoverage C)) :
    Theorem207SheetEssentialAfterDeletion
      (fun p => exists d : Fin C.directionCount, P.PairSeparates p d)
      E := by
  let d := C.first
  constructor
  · refine ⟨d, ?_⟩
    have hpos := (SignedActualSATRunSemantics.ofCoverage C).positive_run_accepts d
    have hneg := (SignedActualSATRunSemantics.ofCoverage C).negative_run_rejects d
    exact (P.full_pair_exact d).2 ⟨hpos, hneg⟩
  · intro hacc
    rcases hacc with ⟨e, hsep⟩
    exact P.remainder_loses_all_pairs e hsep

end SignedExtractionRemainderPairSemantics

/-! ## Remainder-sensitive tri-aspect bridge -/

/-- Remainder-sensitive tri-aspect semantic interface.

The hard field is the transport theorem: actual signed SAT run semantics must
be interpreted by the paper split `full = sheet + remainder`, and the
remainder must lose the intervention separations. -/
structure SignedExtractionRemainderTriAspectSemanticInterface
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (E : Theorem207ExtractionWithRemainder M n hn hn2 htb hns)
    (C : SignedCounterfactualEKPDirectionCoverage enc M n) : Type where
  instrumented_semantics_transport :
    forall A : SignedActualSATRunSemantics C,
      SignedExtractionRemainderPairSemantics E C A

namespace SignedExtractionRemainderTriAspectSemanticInterface

def toSignedExtractionRemainderPairSemantics
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {E : Theorem207ExtractionWithRemainder M n hn hn2 htb hns}
    {C : SignedCounterfactualEKPDirectionCoverage enc M n}
    (I : SignedExtractionRemainderTriAspectSemanticInterface E C) :
    SignedExtractionRemainderPairSemantics E C
      (SignedActualSATRunSemantics.ofCoverage C) :=
  I.instrumented_semantics_transport (SignedActualSATRunSemantics.ofCoverage C)

/-- The remainder-sensitive interface proves deletion essentiality. -/
theorem sheetEssentialityAfterDeletion
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {E : Theorem207ExtractionWithRemainder M n hn hn2 htb hns}
    {C : SignedCounterfactualEKPDirectionCoverage enc M n}
    (I : SignedExtractionRemainderTriAspectSemanticInterface E C) :
    Theorem207SheetEssentialAfterDeletion
      (fun p => exists d : Fin C.directionCount,
        (toSignedExtractionRemainderPairSemantics I).PairSeparates p d)
      E :=
  (toSignedExtractionRemainderPairSemantics I).sheetEssentialityAfterDeletion

end SignedExtractionRemainderTriAspectSemanticInterface

/-- Canonical signed remainder bridge target.

This is the corrected bridge target: full separates, deleted-sheet remainder
loses.  It replaces the earlier sheet-loses polarity. -/
structure CanonicalSignedExtractionRemainderTriAspectBridge
    (enc : SignedFormulaEncoding) : Type where
  interface :
    forall {M : DTM} {n : Nat}
      {hn : n >= 2 ^ 804} {hn2 : n >= 2}
      {htb : M.timeBound <= 4} {hns : M.numStates <= n}
      (E : Theorem207ExtractionWithRemainder M n hn hn2 htb hns)
      (C : SignedCounterfactualEKPDirectionCoverage enc M n),
        Nonempty (SignedExtractionRemainderTriAspectSemanticInterface E C)

/-- The canonical remainder bridge yields deletion essentiality for the
explicit sheet/remainder split. -/
theorem sheetEssentialityAfterDeletion_of_canonicalSignedRemainderBridge
    (enc : SignedFormulaEncoding)
    (H : CanonicalSignedExtractionRemainderTriAspectBridge enc)
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (E : Theorem207ExtractionWithRemainder M n hn hn2 htb hns)
    (C : SignedCounterfactualEKPDirectionCoverage enc M n) :
    Exists (fun Accepts =>
      Theorem207SheetEssentialAfterDeletion Accepts E) := by
  rcases H.interface E C with ⟨I⟩
  exact ⟨
    (fun p => exists d : Fin C.directionCount,
      (I.toSignedExtractionRemainderPairSemantics).PairSeparates p d),
    I.sheetEssentialityAfterDeletion
  ⟩

/-- The corrected bridge works over the concrete non-vacuous signed 3-CNF
encoding added in the preceding file. -/
theorem signedThreeCNFEncoding_remainder_route_nonvacuous :
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

#print axioms Theorem207ExtractionWithRemainder.toExtraction
#print axioms SignedExtractionRemainderPairSemantics.sheetEssentialityAfterDeletion
#print axioms SignedExtractionRemainderTriAspectSemanticInterface.toSignedExtractionRemainderPairSemantics
#print axioms SignedExtractionRemainderTriAspectSemanticInterface.sheetEssentialityAfterDeletion
#print axioms sheetEssentialityAfterDeletion_of_canonicalSignedRemainderBridge
#print axioms signedThreeCNFEncoding_remainder_route_nonvacuous

end PallLean.Paper93.DeepMath.PathB
