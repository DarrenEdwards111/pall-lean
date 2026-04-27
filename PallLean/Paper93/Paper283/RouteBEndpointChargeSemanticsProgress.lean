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

/-! ## Axiom audit anchors -/

#print axioms PaperEndpointChargeSemantics.refines_concreteWEndpointSpanOneStepCharge
#print axioms PaperEndpointChargeSemantics.endpointSpanOneStepChargeCompatible
#print axioms concreteWEndpointSpanOneStepCharge_paperEndpointChargeSemantics
#print axioms endpointAugmentedConcreteW_chargedShiftClosure_of_paperEndpointChargeSemantics
#print axioms endpointAugmentedConcreteW_correctedLocalClosure_of_paperEndpointChargeSemantics_components
#print axioms routeBRicherGauge_endpointChargedPWindowBridge_of_paperEndpointChargeSemantics_zeroProfileCommonSpan
#print axioms routeBRicherGauge_endpointChargedPWindowBridge_of_paperEndpointChargeSemantics_zeroNonScalarCardBound

end PallLean.Paper93.Paper283
