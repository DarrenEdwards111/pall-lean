import PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiExtraction
import PallLean.Paper93.Paper283.RouteBZeroProfileQuotientedCompressionProof
import PallLean.Paper93.DeepMath.PathB.ZeroProfileConcreteNormalFormProgress

/-!
# Strict `TΦ` singleton-quotient final hook

This file specializes the strict `TΦ` projected/log-window consumer to the
exact singleton-quotient zero-profile target.  It keeps the final proof gate
honest: the remaining assumptions are precisely the projected quotient budget
and the strict `TΦ` projected P-window containment.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Strict `TΦ` contradiction from the exact singleton-quotient zero-profile
budget and strict projected P-window containment. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_projectedTypeBudget
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
        withinProfileBound (Nat.log 2 n))
    (hcontrol :
      RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_zeroProfileQuotientedShiftCommonSpan
    M n hn hn2 htb hns hdec
    (zeroProfileQuotientBySingletonShiftProjection
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
    (cookLevinZeroProfileQuotientedShiftCommonSpan_of_singletonQuotient_projectedTypeBudget
      M n hn2 htb hns hbudget)
    hcontrol

/-- Strict `TΦ` contradiction from a concrete singleton-quotient normal-form
classifier plus the exact strict-FOB derivative-erasure row identity. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_concreteSingletonQuotient_strictFOB
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    {typeBudget : Nat}
    (D :
      ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget)
    (hmap :
      ZeroProfileConcreteNormalFormRowMap
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        D)
    (hbudget : typeBudget <= withinProfileBound (Nat.log 2 n))
    (herase :
      RouteBPaperFaithfulTPhiProjectedPWindowStrictFOBDerivativeErasure
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_projectedTypeBudget
    M n hn hn2 htb hns hdec
    (zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_concreteRowMap
      M n hn2 htb hns D hmap hbudget)
    (routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_strictFOBDerivativeErasure
      M n hn2 htb hns
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
      herase)

/-- Uniform strict `TΦ` singleton-quotient projected gates rule out bounded SAT
deciders at paper scale. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_projectedTypeBudget
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
          withinProfileBound (Nat.log 2 n) ∧
        RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
          M n hn2 htb hns
          (zeroProfileQuotientBySingletonShiftProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_projectedTypeBudget
      M n hn hn2 htb hns hdec
      (hcert M n hn hn2 htb hns hdec).1
      (hcert M n hn hn2 htb hns hdec).2

/-- Uniform concrete normal-form classifiers plus strict-FOB row erasure rule
out bounded SAT deciders at paper scale through the strict `TΦ` route. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteSingletonQuotient_strictFOB
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists typeBudget : Nat,
        exists D :
          ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget,
        exists _ :
          ZeroProfileConcreteNormalFormRowMap
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
              (zeroProfileQuotientBySingletonShiftProjection
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
              D,
            typeBudget <= withinProfileBound (Nat.log 2 n) ∧
            RouteBPaperFaithfulTPhiProjectedPWindowStrictFOBDerivativeErasure
              M n hn2 htb hns
              (zeroProfileQuotientBySingletonShiftProjection
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨typeBudget, D, hmap, hbudget, herase⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_concreteSingletonQuotient_strictFOB
      M n hn hn2 htb hns hdec D hmap hbudget herase

/-- Legacy rich-projection discharge from the strict `TΦ` singleton-quotient
projected route, mediated only by the no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_projectedTypeBudget
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
          withinProfileBound (Nat.log 2 n) ∧
        RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
          M n hn2 htb hns
          (zeroProfileQuotientBySingletonShiftProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_projectedTypeBudget
      hcert)

/-- Legacy rich-projection discharge from concrete singleton-quotient
normal-form classifiers and strict-FOB row erasure, mediated only by the
no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_concreteSingletonQuotient_strictFOB
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists typeBudget : Nat,
        exists D :
          ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget,
        exists _ :
          ZeroProfileConcreteNormalFormRowMap
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
              (zeroProfileQuotientBySingletonShiftProjection
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
              D,
            typeBudget <= withinProfileBound (Nat.log 2 n) ∧
            RouteBPaperFaithfulTPhiProjectedPWindowStrictFOBDerivativeErasure
              M n hn2 htb hns
              (zeroProfileQuotientBySingletonShiftProjection
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteSingletonQuotient_strictFOB
      hcert)

/-! ## Axiom audit anchors -/

#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_projectedTypeBudget
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_concreteSingletonQuotient_strictFOB
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_projectedTypeBudget
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteSingletonQuotient_strictFOB
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_projectedTypeBudget
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_concreteSingletonQuotient_strictFOB

end PallLean.Paper93.Paper283
