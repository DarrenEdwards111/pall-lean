import PallLean.Paper93.Paper283.RouteBChargedShiftClosureProgress

/-!
# Route B endpoint charge semantics progress

This file records the paper-facing endpoint charge criterion recoverable from
the current Route B endpoint formalisation.

No external semantic charge relation is asserted here.  Instead, a candidate
`ProfileCharge` must expose the endpoint-span shift and the one-coordinate
histogram bump used by the already checked concrete endpoint route.  Those
fields prove that the candidate refines `concreteWEndpointSpanOneStepCharge`,
and therefore plugs into the endpoint-augmented charged closure and P-window
bridge.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open SymmetricPowerBound
open PallLean.Paper93
open TuringMachine
open PallLean.Paper93.Closure
open PallLean.Paper93.DeepMath.PathB
open WithinProfileBound

attribute [local instance] Classical.dec

/-! ## Semantic endpoint charge fields -/

/-- The endpoint charge semantics currently determined by the formal route.

A candidate paper charge must choose the charged constraint type for each
charged step, put the shift itself in the endpoint repair span, bump exactly
that type's profile coordinate by one, and leave every other profile
coordinate unchanged.  This is intentionally a criterion, not an assertion
that some external paper relation has already been identified in-tree. -/
structure PaperEndpointChargeSemantics
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n) where
  chargedType :
    ∀ (bpSrc bpTgt : BoundedProfile (Nat.log 2 n))
      (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ),
      charge bpSrc S shift bpTgt → ConstraintType
  shift_mem_endpointSpan :
    ∀ (bpSrc bpTgt : BoundedProfile (Nat.log 2 n))
      (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
      (_hcharge : charge bpSrc S shift bpTgt),
      shift ∈ concreteWEndpointSpan n hn4
  target_bump :
    ∀ (bpSrc bpTgt : BoundedProfile (Nat.log 2 n))
      (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
      (hcharge : charge bpSrc S shift bpTgt),
      bpTgt.toHistogram
          (chargedType bpSrc bpTgt S shift hcharge) =
        bpSrc.toHistogram
          (chargedType bpSrc bpTgt S shift hcharge) + 1
  target_same :
    ∀ (bpSrc bpTgt : BoundedProfile (Nat.log 2 n))
      (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
      (hcharge : charge bpSrc S shift bpTgt),
      ∀ τ : ConstraintType,
        τ ≠ chargedType bpSrc bpTgt S shift hcharge →
          bpTgt.toHistogram τ = bpSrc.toHistogram τ

/-- A charge satisfying the semantic endpoint fields refines the concrete
one-step endpoint-span charge relation. -/
theorem PaperEndpointChargeSemantics.refines_concreteWEndpointSpanOneStepCharge
    {n : ℕ} {hn4 : n ≥ 4} {charge : ProfileCharge n}
    (hSem : PaperEndpointChargeSemantics n hn4 charge) :
    ∀ (bpSrc : BoundedProfile (Nat.log 2 n))
      (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
      (bpTgt : BoundedProfile (Nat.log 2 n)),
      charge bpSrc S shift bpTgt →
        concreteWEndpointSpanOneStepCharge n hn4 bpSrc S shift bpTgt := by
  intro bpSrc S shift bpTgt hcharge
  refine
    ⟨hSem.chargedType bpSrc bpTgt S shift hcharge,
      hSem.shift_mem_endpointSpan bpSrc bpTgt S shift hcharge,
      hSem.target_bump bpSrc bpTgt S shift hcharge,
      hSem.target_same bpSrc bpTgt S shift hcharge⟩

/-- The semantic endpoint fields imply the exact one-step compatibility
criterion consumed by the endpoint charged-closure proof. -/
theorem PaperEndpointChargeSemantics.endpointSpanOneStepChargeCompatible
    {n : ℕ} {hn4 : n ≥ 4} {charge : ProfileCharge n}
    (hSem : PaperEndpointChargeSemantics n hn4 charge) :
    EndpointAugmentedConcreteWEndpointSpanOneStepChargeCompatible
      n hn4 charge := by
  intro bpSrc bpTgt S _hSlen shift _hshift hcharge
  exact
    hSem.refines_concreteWEndpointSpanOneStepCharge
      bpSrc S shift bpTgt hcharge

/-- The checked concrete endpoint-span charge itself satisfies the semantic
endpoint charge fields. -/
noncomputable def concreteWEndpointSpanOneStepCharge_paperEndpointChargeSemantics
    (n : ℕ) (hn4 : n ≥ 4) :
    PaperEndpointChargeSemantics
      n hn4 (concreteWEndpointSpanOneStepCharge n hn4) where
  chargedType := fun _bpSrc _bpTgt _S _shift hcharge =>
    Classical.choose hcharge
  shift_mem_endpointSpan := fun _bpSrc _bpTgt _S _shift hcharge =>
    (Classical.choose_spec hcharge).1
  target_bump := fun _bpSrc _bpTgt _S _shift hcharge =>
    (Classical.choose_spec hcharge).2.1
  target_same := fun _bpSrc _bpTgt _S _shift hcharge =>
    (Classical.choose_spec hcharge).2.2

/-! ## Minimal downstream instantiation surface -/

/-- Minimal paper-charge refinement obligation.

If a later file identifies the paper's semantic endpoint-charge relation as a
`ProfileCharge`, this is the exact local fact needed by Route B: every semantic
charged move is one of the checked concrete one-step endpoint-span moves.  This
does not assert that such a semantic charge has already been identified. -/
def PaperEndpointChargeRefinesConcrete
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n) : Prop :=
  ∀ (bpSrc : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (bpTgt : BoundedProfile (Nat.log 2 n)),
      charge bpSrc S shift bpTgt →
        concreteWEndpointSpanOneStepCharge n hn4 bpSrc S shift bpTgt

/-- Stronger equivalence package for a future identified paper charge.

Use this only after the intended paper semantic relation has actually been
defined; the current tree only has the concrete endpoint-span charge. -/
def PaperEndpointChargeEquivalentConcrete
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n) : Prop :=
  ∀ (bpSrc : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (bpTgt : BoundedProfile (Nat.log 2 n)),
      charge bpSrc S shift bpTgt ↔
        concreteWEndpointSpanOneStepCharge n hn4 bpSrc S shift bpTgt

/-- The field-level semantic endpoint criterion implies the minimal downstream
refinement obligation. -/
theorem PaperEndpointChargeSemantics.refinesConcrete
    {n : ℕ} {hn4 : n ≥ 4} {charge : ProfileCharge n}
    (hSem : PaperEndpointChargeSemantics n hn4 charge) :
    PaperEndpointChargeRefinesConcrete n hn4 charge :=
  hSem.refines_concreteWEndpointSpanOneStepCharge

/-- Equivalence with the checked concrete charge implies refinement to it. -/
theorem PaperEndpointChargeEquivalentConcrete.refinesConcrete
    {n : ℕ} {hn4 : n ≥ 4} {charge : ProfileCharge n}
    (hEq : PaperEndpointChargeEquivalentConcrete n hn4 charge) :
    PaperEndpointChargeRefinesConcrete n hn4 charge := by
  intro bpSrc S shift bpTgt hcharge
  exact (hEq bpSrc S shift bpTgt).1 hcharge

/-- Concrete one-step endpoint-span charge refines itself. -/
theorem concreteWEndpointSpanOneStepCharge_refinesConcrete
    (n : ℕ) (hn4 : n ≥ 4) :
    PaperEndpointChargeRefinesConcrete
      n hn4 (concreteWEndpointSpanOneStepCharge n hn4) := by
  intro bpSrc S shift bpTgt hcharge
  exact hcharge

/-- Concrete one-step endpoint-span charge is definitionally equivalent to
itself as a paper-charge instantiation target. -/
theorem concreteWEndpointSpanOneStepCharge_equivalentConcrete
    (n : ℕ) (hn4 : n ≥ 4) :
    PaperEndpointChargeEquivalentConcrete
      n hn4 (concreteWEndpointSpanOneStepCharge n hn4) := by
  intro bpSrc S shift bpTgt
  rfl

/-- The minimal refinement obligation is exactly enough to feed the existing
one-step endpoint-span compatibility theorem. -/
theorem endpointAugmentedConcreteW_endpointSpanOneStepChargeCompatible_of_paperEndpointChargeRefinesConcrete
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hRef : PaperEndpointChargeRefinesConcrete n hn4 charge) :
    EndpointAugmentedConcreteWEndpointSpanOneStepChargeCompatible
      n hn4 charge := by
  intro bpSrc bpTgt S _hSlen shift _hshift hcharge
  exact hRef bpSrc S shift bpTgt hcharge

/-- A future paper endpoint charge only has to refine the concrete one-step
endpoint-span charge to obtain the full charged shift closure. -/
theorem endpointAugmentedConcreteW_chargedShiftClosure_of_paperEndpointChargeRefinesConcrete
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hRef : PaperEndpointChargeRefinesConcrete n hn4 charge) :
    EndpointAugmentedConcreteWChargedShiftClosure n hn4 charge :=
  endpointAugmentedConcreteW_chargedShiftClosure_of_oneStepChargeCompatible
    n hn4 charge
    (endpointAugmentedConcreteW_endpointSpanOneStepChargeCompatible_of_paperEndpointChargeRefinesConcrete
      n hn4 charge hRef)

/-- Packaged endpoint charge instantiation for downstream Route B assembly.

This is the paper-facing surface to consume once a semantic endpoint charge is
chosen.  The package stores the chosen `ProfileCharge` and only the refinement
fact Route B truly uses. -/
structure PaperEndpointChargeInstantiation
    (n : ℕ) (hn4 : n ≥ 4) where
  charge : ProfileCharge n
  refinesConcrete : PaperEndpointChargeRefinesConcrete n hn4 charge

namespace PaperEndpointChargeInstantiation

/-- Build the downstream instantiation package from the field-level semantic
criterion. -/
def ofSemantics
    {n : ℕ} {hn4 : n ≥ 4} (charge : ProfileCharge n)
    (hSem : PaperEndpointChargeSemantics n hn4 charge) :
    PaperEndpointChargeInstantiation n hn4 where
  charge := charge
  refinesConcrete := hSem.refinesConcrete

/-- Build the downstream instantiation package from a future equivalence proof
against the concrete endpoint-span charge. -/
def ofEquivalentConcrete
    {n : ℕ} {hn4 : n ≥ 4} (charge : ProfileCharge n)
    (hEq : PaperEndpointChargeEquivalentConcrete n hn4 charge) :
    PaperEndpointChargeInstantiation n hn4 where
  charge := charge
  refinesConcrete := hEq.refinesConcrete

/-- The concrete endpoint-span charge as the already checked instantiation. -/
def concrete
    (n : ℕ) (hn4 : n ≥ 4) :
    PaperEndpointChargeInstantiation n hn4 where
  charge := concreteWEndpointSpanOneStepCharge n hn4
  refinesConcrete := concreteWEndpointSpanOneStepCharge_refinesConcrete n hn4

/-- The packaged refinement gives the one-step endpoint-span compatibility. -/
theorem endpointSpanOneStepChargeCompatible
    {n : ℕ} {hn4 : n ≥ 4}
    (hInst : PaperEndpointChargeInstantiation n hn4) :
    EndpointAugmentedConcreteWEndpointSpanOneStepChargeCompatible
      n hn4 hInst.charge :=
  endpointAugmentedConcreteW_endpointSpanOneStepChargeCompatible_of_paperEndpointChargeRefinesConcrete
    n hn4 hInst.charge hInst.refinesConcrete

/-- The packaged refinement gives the full endpoint-augmented charged closure. -/
theorem chargedShiftClosure
    {n : ℕ} {hn4 : n ≥ 4}
    (hInst : PaperEndpointChargeInstantiation n hn4) :
    EndpointAugmentedConcreteWChargedShiftClosure n hn4 hInst.charge :=
  endpointAugmentedConcreteW_chargedShiftClosure_of_paperEndpointChargeRefinesConcrete
    n hn4 hInst.charge hInst.refinesConcrete

/-- Component wrapper using a packaged paper endpoint charge instantiation. -/
theorem correctedLocalClosure_of_components
    {n : ℕ} {hn4 : n ≥ 4}
    (hInst : PaperEndpointChargeInstantiation n hn4)
    (hI1 :
      PerTypeProductGrouping (n := n) (endpointAugmentedConcreteW n hn4))
    (hI3 :
      PerTypeMlprojClosure (n := n) (endpointAugmentedConcreteW n hn4)) :
    EndpointAugmentedConcreteWCorrectedLocalClosure n hn4 hInst.charge :=
  endpointAugmentedConcreteW_correctedLocalClosure_of_charged_components
    n hn4 hInst.charge hI1 hInst.chargedShiftClosure hI3

end PaperEndpointChargeInstantiation

/-! ## Plug-in theorems for the wired endpoint route -/

/-- Any charge satisfying the endpoint semantic fields has the full
endpoint-augmented charged shift closure. -/
theorem endpointAugmentedConcreteW_chargedShiftClosure_of_paperEndpointChargeSemantics
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hSem : PaperEndpointChargeSemantics n hn4 charge) :
    EndpointAugmentedConcreteWChargedShiftClosure n hn4 charge :=
  endpointAugmentedConcreteW_chargedShiftClosure_of_oneStepChargeCompatible
    n hn4 charge hSem.endpointSpanOneStepChargeCompatible

/-- Component wrapper: endpoint H4 and universal charged I5 close locally for
any semantically compatible endpoint charge. -/
theorem endpointAugmentedConcreteW_correctedLocalClosure_of_paperEndpointChargeSemantics_components
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hSem : PaperEndpointChargeSemantics n hn4 charge)
    (hI1 :
      PerTypeProductGrouping (n := n) (endpointAugmentedConcreteW n hn4))
    (hI3 :
      PerTypeMlprojClosure (n := n) (endpointAugmentedConcreteW n hn4)) :
    EndpointAugmentedConcreteWCorrectedLocalClosure n hn4 charge :=
  endpointAugmentedConcreteW_correctedLocalClosure_of_charged_components
    n hn4 charge hI1
    (endpointAugmentedConcreteW_chargedShiftClosure_of_paperEndpointChargeSemantics
      n hn4 charge hSem)
    hI3

/-- Direct zero-profile-common-span P-window bridge for any endpoint charge
satisfying the semantic fields. -/
noncomputable def routeBRicherGauge_endpointChargedPWindowBridge_of_paperEndpointChargeSemantics_zeroProfileCommonSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4) (charge : ProfileCharge n)
    (hSem : PaperEndpointChargeSemantics n hn4 charge)
    (hI1 :
      PerTypeProductGrouping (n := n) (endpointAugmentedConcreteW n hn4))
    (hI3 :
      PerTypeMlprojClosure (n := n) (endpointAugmentedConcreteW n hn4))
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    RouteBRicherGaugeEndpointChargedPWindowBridge
      M n hn2 htb hns hn4 charge :=
  routeBRicherGauge_endpointChargedPWindowBridge_of_activeTypeCaseBlockers_zeroProfileCommonSpan
    M n hn2 htb hns hn4 charge hI1
    (endpointAugmentedConcreteW_chargedShiftClosure_of_paperEndpointChargeSemantics
      n hn4 charge hSem)
    hI3 hzero hactive

/-- Cardinality-bound P-window bridge for any endpoint charge satisfying the
semantic fields.  This is the same endpoint route used by the concrete
one-step charge, with the charge left abstract behind the checked criterion. -/
noncomputable def routeBRicherGauge_endpointChargedPWindowBridge_of_paperEndpointChargeSemantics_zeroNonScalarCardBound
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4) (charge : ProfileCharge n)
    (hSem : PaperEndpointChargeSemantics n hn4 charge)
    (hI1 :
      PerTypeProductGrouping (n := n) (endpointAugmentedConcreteW n hn4))
    (hI3 :
      PerTypeMlprojClosure (n := n) (endpointAugmentedConcreteW n hn4))
    (hbound :
      cookLevinZeroProfileNonScalarCardBound M n hn2 htb hns <=
        withinProfileBound (Nat.log 2 n))
    (hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    RouteBRicherGaugeEndpointChargedPWindowBridge
      M n hn2 htb hns hn4 charge :=
  routeBRicherGauge_endpointChargedPWindowBridge_of_activeTypeCaseBlockers_zeroNonScalarCardBound
    M n hn2 htb hns hn4 charge hI1
    (endpointAugmentedConcreteW_chargedShiftClosure_of_paperEndpointChargeSemantics
      n hn4 charge hSem)
    hI3 hbound hactive

/-! ## Downstream wrappers for a packaged paper-charge instantiation -/

/-- Direct zero-profile-common-span P-window bridge for a packaged paper
endpoint charge instantiation. -/
noncomputable def routeBRicherGauge_endpointChargedPWindowBridge_of_paperEndpointChargeInstantiation_zeroProfileCommonSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hInst : PaperEndpointChargeInstantiation n hn4)
    (hI1 :
      PerTypeProductGrouping (n := n) (endpointAugmentedConcreteW n hn4))
    (hI3 :
      PerTypeMlprojClosure (n := n) (endpointAugmentedConcreteW n hn4))
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    RouteBRicherGaugeEndpointChargedPWindowBridge
      M n hn2 htb hns hn4 hInst.charge :=
  routeBRicherGauge_endpointChargedPWindowBridge_of_activeTypeCaseBlockers_zeroProfileCommonSpan
    M n hn2 htb hns hn4 hInst.charge hI1
    hInst.chargedShiftClosure hI3 hzero hactive

/-- Cardinality-bound P-window bridge for a packaged paper endpoint charge
instantiation.  This wrapper does not identify the paper charge; it exposes the
minimal refinement package needed once the charge is chosen. -/
noncomputable def routeBRicherGauge_endpointChargedPWindowBridge_of_paperEndpointChargeInstantiation_zeroNonScalarCardBound
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hInst : PaperEndpointChargeInstantiation n hn4)
    (hI1 :
      PerTypeProductGrouping (n := n) (endpointAugmentedConcreteW n hn4))
    (hI3 :
      PerTypeMlprojClosure (n := n) (endpointAugmentedConcreteW n hn4))
    (hbound :
      cookLevinZeroProfileNonScalarCardBound M n hn2 htb hns <=
        withinProfileBound (Nat.log 2 n))
    (hactive :
      CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    RouteBRicherGaugeEndpointChargedPWindowBridge
      M n hn2 htb hns hn4 hInst.charge :=
  routeBRicherGauge_endpointChargedPWindowBridge_of_activeTypeCaseBlockers_zeroNonScalarCardBound
    M n hn2 htb hns hn4 hInst.charge hI1
    hInst.chargedShiftClosure hI3 hbound hactive

/-! ## Axiom audit anchors -/

#print axioms PaperEndpointChargeSemantics.refines_concreteWEndpointSpanOneStepCharge
#print axioms PaperEndpointChargeSemantics.endpointSpanOneStepChargeCompatible
#print axioms concreteWEndpointSpanOneStepCharge_paperEndpointChargeSemantics
#print axioms PaperEndpointChargeSemantics.refinesConcrete
#print axioms PaperEndpointChargeEquivalentConcrete.refinesConcrete
#print axioms concreteWEndpointSpanOneStepCharge_refinesConcrete
#print axioms concreteWEndpointSpanOneStepCharge_equivalentConcrete
#print axioms endpointAugmentedConcreteW_endpointSpanOneStepChargeCompatible_of_paperEndpointChargeRefinesConcrete
#print axioms endpointAugmentedConcreteW_chargedShiftClosure_of_paperEndpointChargeRefinesConcrete
#print axioms PaperEndpointChargeInstantiation.ofSemantics
#print axioms PaperEndpointChargeInstantiation.ofEquivalentConcrete
#print axioms PaperEndpointChargeInstantiation.concrete
#print axioms PaperEndpointChargeInstantiation.endpointSpanOneStepChargeCompatible
#print axioms PaperEndpointChargeInstantiation.chargedShiftClosure
#print axioms PaperEndpointChargeInstantiation.correctedLocalClosure_of_components
#print axioms endpointAugmentedConcreteW_chargedShiftClosure_of_paperEndpointChargeSemantics
#print axioms endpointAugmentedConcreteW_correctedLocalClosure_of_paperEndpointChargeSemantics_components
#print axioms routeBRicherGauge_endpointChargedPWindowBridge_of_paperEndpointChargeSemantics_zeroProfileCommonSpan
#print axioms routeBRicherGauge_endpointChargedPWindowBridge_of_paperEndpointChargeSemantics_zeroNonScalarCardBound
#print axioms routeBRicherGauge_endpointChargedPWindowBridge_of_paperEndpointChargeInstantiation_zeroProfileCommonSpan
#print axioms routeBRicherGauge_endpointChargedPWindowBridge_of_paperEndpointChargeInstantiation_zeroNonScalarCardBound

end PallLean.Paper93.Paper283
