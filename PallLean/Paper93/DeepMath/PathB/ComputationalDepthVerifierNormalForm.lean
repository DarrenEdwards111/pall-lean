import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRemainderTriAspectSemanticInterface

/-!
# Canonical verifier normal-form surface

The previous remainder-sensitive route exposes the right local theorem:

* the full paper object separates signed SAT/UNSAT intervention pairs;
* the deleted-sheet remainder loses those separations;
* therefore the extracted sheet is essential after deletion.

That still does not force an arbitrary SAT decider to realize the sheet.  This
file records the sharper, non-black-box target:

1. transform any signed SAT decider `M` into a canonical verifier-normal-form
   decider `M#`;
2. prove the remainder-sensitive transport syntactically for that normal form.

No such transformation is proved here.  The point is to make the new
load-bearing theorem explicit and to keep it separate from the already-proved
remainder wiring.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-! ## Signed SAT decision and polynomial-overhead wrappers -/

/-- A signed SAT decider for a formula encoding.

This is the signed analogue of the earlier SAT-decision sockets: on every
encoded signed formula, the DTM acceptance bit agrees with satisfiability. -/
def SignedDTMDecidesSAT (enc : SignedFormulaEncoding) (M : DTM) : Prop :=
  forall {n : Nat} (hn : n >= 1)
    (input : Fin n -> Bool) (φ : enc.Formula),
      enc.Encodes input φ ->
        (TuringMachine.accepts M n hn input <-> enc.Satisfiable φ)

/-- Coarse polynomial-overhead predicate for the normal-form wrapper.

This file only needs a named interface saying that the wrapped machine remains
in the same polynomial-time regime.  A future concrete wrapper should replace
these coarse bounds by the exact compiler overhead. -/
def PolynomialTimeOverhead (M Msharp : DTM) : Prop :=
  exists overheadExponent : Nat,
    Msharp.timeBound <= M.timeBound + overheadExponent /\
    Msharp.numStates <= M.numStates + overheadExponent

/-! ## Canonical verifier normal form -/

/-- A canonical verifier-normal-form machine.

The first five fields are the Book-1/paper design constraints: the machine has
a signed clause boundary, routes the accept/reject channel through that
boundary, makes the verifier sheet syntactic, and separates the P-side
boundary/control projection from the NP-side sheet.  The last field is the
precise syntactic transport theorem needed by the remainder route.

This avoids the failed claim that an arbitrary black-box decider reveals the
sheet.  The sheet is required only after passing to this explicit normal form. -/
structure CanonicalVerifierNormalForm
    (enc : SignedFormulaEncoding) (M : DTM) : Type where
  exposes_signed_clause_boundary : Prop
  exposes_signed_clause_boundary_cert : exposes_signed_clause_boundary
  routes_acceptance_through_boundary : Prop
  routes_acceptance_through_boundary_cert :
    routes_acceptance_through_boundary
  verifier_sheet_is_syntactic : Prop
  verifier_sheet_is_syntactic_cert : verifier_sheet_is_syntactic
  deletion_removes_pair_channel : Prop
  deletion_removes_pair_channel_cert : deletion_removes_pair_channel
  p_side_boundary_projection_bound : Prop
  p_side_boundary_projection_bound_cert : p_side_boundary_projection_bound
  syntactic_remainder_transport :
    forall {n : Nat}
      {hn : n >= 2 ^ 804} {hn2 : n >= 2}
      {htb : M.timeBound <= 4} {hns : M.numStates <= n}
      (E : CanonicalTheorem207ExtractionWithRemainder M n hn hn2 htb hns)
      (C : SignedCounterfactualEKPDirectionCoverage enc M n),
        Nonempty
          (SignedExtractionRemainderTriAspectSemanticInterface
            E.extraction C)
  fixed_syntactic_remainder_transport :
    forall {n : Nat}
      {hn : n >= 2 ^ 804} {hn2 : n >= 2}
      {htb : M.timeBound <= 4} {hns : M.numStates <= n}
      (E : CanonicalTheorem207ExtractionWithRemainder M n hn hn2 htb hns)
      (C : SignedCounterfactualEKPDirectionCoverage enc M n),
        Nonempty
          (FixedSignedExtractionRemainderTriAspectSemanticInterface
            E.extraction C)

namespace CanonicalVerifierNormalForm

/-- In verifier normal form, the remainder-sensitive semantic transport is a
syntactic consequence of the normal-form data. -/
theorem remainderTransport
    {enc : SignedFormulaEncoding} {M : DTM}
    (Hnf : CanonicalVerifierNormalForm enc M)
    {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (E : CanonicalTheorem207ExtractionWithRemainder M n hn hn2 htb hns)
    (C : SignedCounterfactualEKPDirectionCoverage enc M n) :
    Nonempty
      (SignedExtractionRemainderTriAspectSemanticInterface
        E.extraction C) :=
  Hnf.syntactic_remainder_transport E C

/-- In verifier normal form, the fixed-evaluation remainder transport is a
syntactic consequence of the normal-form data.  This is the non-smuggling
version used by the serious force target. -/
theorem fixedRemainderTransport
    {enc : SignedFormulaEncoding} {M : DTM}
    (Hnf : CanonicalVerifierNormalForm enc M)
    {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (E : CanonicalTheorem207ExtractionWithRemainder M n hn hn2 htb hns)
    (C : SignedCounterfactualEKPDirectionCoverage enc M n) :
    Nonempty
      (FixedSignedExtractionRemainderTriAspectSemanticInterface
        E.extraction C) :=
  Hnf.fixed_syntactic_remainder_transport E C

/-- Verifier-normal-form transport immediately gives deletion essentiality for
the canonical sheet/remainder split. -/
theorem sheetEssentialityAfterDeletion
    {enc : SignedFormulaEncoding} {M : DTM}
    (Hnf : CanonicalVerifierNormalForm enc M)
    {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (E : CanonicalTheorem207ExtractionWithRemainder M n hn hn2 htb hns)
    (C : SignedCounterfactualEKPDirectionCoverage enc M n) :
    Exists (fun Accepts =>
      Theorem207SheetEssentialAfterDeletion Accepts E.extraction) := by
  rcases Hnf.remainderTransport E C with ⟨I⟩
  exact ⟨
    (fun p => exists d : Fin C.directionCount,
      (I.toSignedExtractionRemainderPairSemantics).PairSeparates p d),
    I.sheetEssentialityAfterDeletion
  ⟩

/-- Fixed-evaluation verifier-normal-form transport gives deletion
essentiality without a freely chosen pair-separation predicate. -/
theorem fixedSheetEssentialityAfterDeletion
    {enc : SignedFormulaEncoding} {M : DTM}
    (Hnf : CanonicalVerifierNormalForm enc M)
    {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (E : CanonicalTheorem207ExtractionWithRemainder M n hn hn2 htb hns)
    (C : SignedCounterfactualEKPDirectionCoverage enc M n) :
    Exists (fun Accepts =>
      Theorem207SheetEssentialAfterDeletion Accepts E.extraction) := by
  rcases Hnf.fixedRemainderTransport E C with ⟨I⟩
  exact ⟨
    (fun p => exists d : Fin C.directionCount,
      (I.toFixedSignedExtractionRemainderPairSemantics).evaluation.PairSeparates p d),
    I.sheetEssentialityAfterDeletion
  ⟩

end CanonicalVerifierNormalForm

/-! ## Normal-form transformation target -/

/-- The actual breakthrough target: any signed SAT decider can be wrapped into
a canonical verifier-normal-form decider with polynomial overhead. -/
structure SignedSATDeciderToCanonicalVerifierNormalForm
    (enc : SignedFormulaEncoding) : Type where
  transform : DTM -> DTM
  correctness :
    forall {M : DTM},
      SignedDTMDecidesSAT enc M ->
        SignedDTMDecidesSAT enc (transform M)
  overhead :
    forall M : DTM,
      PolynomialTimeOverhead M (transform M)
  normal_form :
    forall {M : DTM},
      SignedDTMDecidesSAT enc M ->
        CanonicalVerifierNormalForm enc (transform M)

namespace SignedSATDeciderToCanonicalVerifierNormalForm

/-- The normal-form theorem, packaged as the existential statement used by the
P-vs-NP route. -/
theorem normalForm_of_signedSATDecider
    {enc : SignedFormulaEncoding}
    (H : SignedSATDeciderToCanonicalVerifierNormalForm enc)
    {M : DTM}
    (hM : SignedDTMDecidesSAT enc M) :
    exists Msharp : DTM,
      SignedDTMDecidesSAT enc Msharp /\
      PolynomialTimeOverhead M Msharp /\
      Nonempty (CanonicalVerifierNormalForm enc Msharp) := by
  refine ⟨H.transform M, ?_, ?_, ?_⟩
  · exact H.correctness hM
  · exact H.overhead M
  · exact ⟨H.normal_form hM⟩

/-- Composing the wrapper with verifier-normal-form transport gives the
canonical deletion-essentiality endpoint for the wrapped decider. -/
theorem sheetEssentialityAfterDeletion_of_signedSATDecider
    {enc : SignedFormulaEncoding}
    (H : SignedSATDeciderToCanonicalVerifierNormalForm enc)
    {M : DTM}
    (hM : SignedDTMDecidesSAT enc M)
    {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : (H.transform M).timeBound <= 4}
    {hns : (H.transform M).numStates <= n}
    (E :
      CanonicalTheorem207ExtractionWithRemainder
        (H.transform M) n hn hn2 htb hns)
    (C :
      SignedCounterfactualEKPDirectionCoverage
        enc (H.transform M) n) :
    Exists (fun Accepts =>
      Theorem207SheetEssentialAfterDeletion Accepts E.extraction) :=
  (H.normal_form hM).sheetEssentialityAfterDeletion E C

/-- Fixed-evaluation deletion essentiality for the wrapped normal-form decider.
-/
theorem fixedSheetEssentialityAfterDeletion_of_signedSATDecider
    {enc : SignedFormulaEncoding}
    (H : SignedSATDeciderToCanonicalVerifierNormalForm enc)
    {M : DTM}
    (hM : SignedDTMDecidesSAT enc M)
    {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : (H.transform M).timeBound <= 4}
    {hns : (H.transform M).numStates <= n}
    (E :
      CanonicalTheorem207ExtractionWithRemainder
        (H.transform M) n hn hn2 htb hns)
    (C :
      SignedCounterfactualEKPDirectionCoverage
        enc (H.transform M) n) :
    Exists (fun Accepts =>
      Theorem207SheetEssentialAfterDeletion Accepts E.extraction) :=
  (H.normal_form hM).fixedSheetEssentialityAfterDeletion E C

end SignedSATDeciderToCanonicalVerifierNormalForm

/-! ## Kernel-only axiom trace -/

#print axioms CanonicalVerifierNormalForm.remainderTransport
#print axioms CanonicalVerifierNormalForm.fixedRemainderTransport
#print axioms CanonicalVerifierNormalForm.sheetEssentialityAfterDeletion
#print axioms CanonicalVerifierNormalForm.fixedSheetEssentialityAfterDeletion
#print axioms SignedSATDeciderToCanonicalVerifierNormalForm.normalForm_of_signedSATDecider
#print axioms SignedSATDeciderToCanonicalVerifierNormalForm.sheetEssentialityAfterDeletion_of_signedSATDecider
#print axioms SignedSATDeciderToCanonicalVerifierNormalForm.fixedSheetEssentialityAfterDeletion_of_signedSATDecider

end PallLean.Paper93.DeepMath.PathB
