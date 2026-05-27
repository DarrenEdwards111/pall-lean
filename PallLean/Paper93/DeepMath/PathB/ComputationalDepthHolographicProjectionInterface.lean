import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCounterfactualEKP

/-!
# Holographic projection semantic interface

This file records the next honest version of the Book/N-frame proposal:
the Theorem-207 sheet must not be an abstract polynomial with a free
acceptance predicate.  It must be tied to:

* the actual Cook--Levin bulk polynomial for `M,n`;
* a concrete boundary projection of that bulk;
* a semantic pair-separation predicate on actual counterfactual input pairs.

The file proves only the wiring theorem.  If such an interface is supplied,
then the counterfactual actual-pair polynomial semantics from
`ComputationalDepthCounterfactualEKP` follows.  The load-bearing theorem is
therefore exposed as a real Cook--Levin/holographic semantic projection
problem, not as rank or essentiality by definition.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation
open TuringMachine
open MvPolynomial
open InstrumentedSheetAudit

/-! ## Actual Cook--Levin bulk -/

/-- The actual local Cook--Levin bulk polynomial in the current formal model.

This is deliberately not a free field: it is the concrete `compiledPoly` of
the current `cook_levin_compilation M n ...`.  A paper-faithful instrumented
bulk can later replace this by proving an equality/transport theorem into this
surface. -/
noncomputable def actualCookLevinBulkPoly
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ :=
  compiledPoly (cook_levin_compilation M n hn2 htb hns)

/-! ## Holographic semantic projection -/

/-- A semantic holographic interface for a concrete instrumented sheet.

The fields separate three kinds of data:

* **projection substrate**: `paperCompiledPoly` is the actual Cook--Levin bulk,
  and `coupledSheet` is the declared projection image of that bulk;
* **pair semantics**: `PairSeparates p d` says polynomial `p` separates the
  actual positive/negative intervention pair indexed by `d`;
* **semantic force**: actual run facts force the bulk to separate each pair,
  while the projected boundary sheet separates no pair.

This is the linchpin surface: proving it for the canonical N-frame projection
would be a genuine semantic theorem.  None of its fields is a rank lower bound
or `Theorem207SheetEssentialForAcceptance` by definition.
-/
structure HolographicProjectionSemanticInterface
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns)
    (C : CounterfactualEKPDirectionCoverage enc M n) : Type where
  projection :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ
  paperCompiled_is_actual_bulk :
    S.extraction.paperCompiledPoly =
      actualCookLevinBulkPoly M n hn2 htb hns
  coupledSheet_is_projected_bulk :
    S.extraction.coupledSheet =
      projection (actualCookLevinBulkPoly M n hn2 htb hns)
  PairSeparates :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ ->
      Fin C.directionCount -> Prop
  bulk_separates_of_actual_pair :
    forall d : Fin C.directionCount,
      TuringMachine.accepts M n C.hn (C.positiveInput d) ->
      Not (TuringMachine.accepts M n C.hn (C.negativeInput d)) ->
        PairSeparates S.extraction.paperCompiledPoly d
  boundary_loses_all_pairs :
    forall d : Fin C.directionCount,
      Not (PairSeparates S.extraction.coupledSheet d)

namespace HolographicProjectionSemanticInterface

/-- A direction tag map induced by counterfactual EKP labels. -/
def sheetDirection
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {S : InstrumentedTheorem207Sheet M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    (_H : HolographicProjectionSemanticInterface S C) :
    Fin C.directionCount -> Nat :=
  fun d => (C.directionOf d).tag

/-- The tag map is injective because the counterfactual direction map itself is
injective and `CounterfactualEKPDirection` has only the `tag` field. -/
theorem sheetDirection_injective
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {S : InstrumentedTheorem207Sheet M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    (H : HolographicProjectionSemanticInterface S C) :
    Function.Injective (sheetDirection H) := by
  intro a b htag
  have hdir : C.directionOf a = C.directionOf b := by
    cases ha : C.directionOf a with
    | mk taga =>
      cases hb : C.directionOf b with
      | mk tagb =>
        simp [sheetDirection, ha, hb] at htag
        simp [htag]
  exact C.direction_injective hdir

/-- The holographic semantic interface supplies the actual-pair polynomial
semantics used by the counterfactual EKP bridge.

The acceptance predicate is not arbitrary here: `Accepts p` means that `p`
separates at least one actual positive/negative intervention pair.  The full
bulk separates every pair by the actual run facts; the projected boundary sheet
separates no pair by the interface's semantic loss field. -/
def toActualPairPolynomialSemantics
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {S : InstrumentedTheorem207Sheet M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    (H : HolographicProjectionSemanticInterface S C) :
    ActualPairPolynomialSemantics (S := S)
      (ActualCounterfactualPairFacts.ofCoverage C) where
  Accepts := fun p => exists d : Fin C.directionCount, H.PairSeparates p d
  full_poly_accepts_of_pair := by
    intro d hpos
    exact ⟨d, H.bulk_separates_of_actual_pair d hpos (C.negative_not_accepts d)⟩
  deleted_poly_rejects_of_pair := by
    intro _d _hneg hacc
    rcases hacc with ⟨e, hsep⟩
    exact H.boundary_loses_all_pairs e hsep
  sheetDirection := sheetDirection H
  sheetDirection_injective := sheetDirection_injective H

/-- Therefore the holographic projection interface discharges the counterfactual
sheet-binding predicate without defining binding as rank/essentiality. -/
def toSheetBindsCounterfactualSwitches
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {S : InstrumentedTheorem207Sheet M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    (H : HolographicProjectionSemanticInterface S C) :
    SheetBindsCounterfactualSwitches S C :=
  SheetBindsCounterfactualSwitches.ofCoveragePolynomialSemantics
    (toActualPairPolynomialSemantics H)

/-- The final wiring theorem: a concrete holographic projection interface is
enough to produce ordinary Theorem-207 acceptance essentiality. -/
theorem theorem207Essentiality_of_holographicProjectionInterface
    {enc : ThreeCNFEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {S : InstrumentedTheorem207Sheet M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    (H : HolographicProjectionSemanticInterface S C) :
    Theorem207SheetEssentialForAcceptance
      (toActualPairPolynomialSemantics H).Accepts S :=
  theorem207SheetEssentialForAcceptance_of_actualPairPolynomialSemantics
    (toActualPairPolynomialSemantics H)

end HolographicProjectionSemanticInterface

/-! ## Global target shape -/

/-- The global Book/N-frame linchpin after this refactor.

This is the exact theorem a real holographic projection proof would need to
supply: every relevant instrumented sheet and counterfactual intervention
family must carry the concrete semantic projection interface above. -/
structure HolographicProjectionSemanticBridge
    (enc : ThreeCNFEncoding) : Type where
  interface :
    forall {M : DTM} {n : Nat}
      {hn : n >= 2 ^ 804} {hn2 : n >= 2}
      {htb : M.timeBound <= 4} {hns : M.numStates <= n}
      (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns)
      (C : CounterfactualEKPDirectionCoverage enc M n),
        Nonempty (HolographicProjectionSemanticInterface S C)

/-- A global holographic projection bridge recovers the existing
counterfactual essentiality bridge. -/
def counterfactualBridge_of_holographicProjectionSemanticBridge
    (enc : ThreeCNFEncoding)
    (H : HolographicProjectionSemanticBridge enc) :
    CounterfactualEKPToTheorem207Essentiality enc where
  bind := by
    intro M n hn hn2 htb hns S C
    rcases H.interface S C with ⟨I⟩
    exact ⟨I.toSheetBindsCounterfactualSwitches⟩

/-! ## Kernel-only axiom trace -/

#print axioms HolographicProjectionSemanticInterface.sheetDirection_injective
#print axioms HolographicProjectionSemanticInterface.toActualPairPolynomialSemantics
#print axioms HolographicProjectionSemanticInterface.toSheetBindsCounterfactualSwitches
#print axioms HolographicProjectionSemanticInterface.theorem207Essentiality_of_holographicProjectionInterface
#print axioms counterfactualBridge_of_holographicProjectionSemanticBridge

end PallLean.Paper93.DeepMath.PathB
