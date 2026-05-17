import PallLean.Paper93.DeepMath.PathC.PiPlusProjectedPayloadCloseout
import PallLean.Paper93.DeepMath.PathB.ZeroProfileFiniteNormalFormClassifier

/-!
# Nontrivial projected zero-profile frontier

The zero projection discharges the *weak* projected socket, but it is not the
mathematical zero-profile payload.  For the canonical singleton quotient this
file pins down the real target exactly: the projected zero-profile socket is
equivalent to the exact projected quotient finrank fitting inside the one-window
within-profile budget.

So the remaining nontrivial zero-profile work is no longer vague; it is the
single arithmetic/algebraic bound

`zeroProfileSingletonQuotientProjectedTypeBudget (log₂ n + 1) factors ≤
 withinProfileBound (log₂ n + 1)`.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- Generic singleton-quotient projected common span from the exact projected
quotient budget bound. -/
theorem zeroProfileProjectedCommonSpanWithBudget_singletonQuotient_of_exactBudget_le
    {n L κ budget : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget κ factors ≤ budget) :
    ZeroProfileProjectedCommonSpanWithBudget κ factors
      (zeroProfileQuotientBySingletonShiftProjection factors) budget := by
  classical
  rcases zeroProfileProjectedCommonSpanWithBudget_singletonQuotient_projectedFinrank
      κ factors with ⟨G, hG_card, hG_span⟩
  exact ⟨G, hG_card.trans hbudget, hG_span⟩

/-- For the singleton quotient, the projected common-span socket is exactly the
exact projected quotient finrank budget inequality. -/
theorem zeroProfileProjectedCommonSpanWithBudget_singletonQuotient_iff_exactBudget_le
    {n L κ budget : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) :
    ZeroProfileProjectedCommonSpanWithBudget κ factors
        (zeroProfileQuotientBySingletonShiftProjection factors) budget ↔
      zeroProfileSingletonQuotientProjectedTypeBudget κ factors ≤ budget := by
  constructor
  · intro hspan
    simpa [zeroProfileSingletonQuotientProjectedTypeBudget] using
      zeroProfileProjectedShiftSpan_finrank_le_of_commonSpanWithBudget_core
        factors (zeroProfileQuotientBySingletonShiftProjection factors) hspan
  · intro hbudget
    exact zeroProfileProjectedCommonSpanWithBudget_singletonQuotient_of_exactBudget_le
      factors hbudget

/-- The paper-scale singleton-quotient projected zero-profile socket follows
from the exact one-window projected quotient budget bound. -/
theorem paperScaleSingletonQuotient_projectedZeroCommonSpan_of_exactBudget_le
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget
          (Nat.log 2 (2 ^ 804) + 1)
          (fun i =>
            (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i) ≤
        withinProfileBound (Nat.log 2 (2 ^ 804) + 1)) :
    PaperScaleCookLevinOneWindowProjectedZeroHistogramShiftCommonSpan
      M htb hns
      (paperScaleCookLevinSingletonQuotientProjection M htb hns) := by
  change ZeroProfileProjectedCommonSpanWithBudget
    (Nat.log 2 (2 ^ 804) + 1)
    (fun i =>
      (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i)
    (zeroProfileQuotientBySingletonShiftProjection
      (fun i =>
        (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i))
    (withinProfileBound (Nat.log 2 (2 ^ 804) + 1))
  exact
    zeroProfileProjectedCommonSpanWithBudget_singletonQuotient_of_exactBudget_le
      (κ := Nat.log 2 (2 ^ 804) + 1)
      (factors := fun i =>
        (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i)
      hbudget

/-- Conversely, any paper-scale singleton-quotient projected zero-profile common
span proves exactly the one-window projected quotient budget bound. -/
theorem exactBudget_le_of_paperScaleSingletonQuotient_projectedZeroCommonSpan
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hspan :
      PaperScaleCookLevinOneWindowProjectedZeroHistogramShiftCommonSpan
        M htb hns
        (paperScaleCookLevinSingletonQuotientProjection M htb hns)) :
    zeroProfileSingletonQuotientProjectedTypeBudget
        (Nat.log 2 (2 ^ 804) + 1)
        (fun i =>
          (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i) ≤
      withinProfileBound (Nat.log 2 (2 ^ 804) + 1) := by
  have hiff :=
    zeroProfileProjectedCommonSpanWithBudget_singletonQuotient_iff_exactBudget_le
      (κ := Nat.log 2 (2 ^ 804) + 1)
      (budget := withinProfileBound (Nat.log 2 (2 ^ 804) + 1))
      (factors := fun i =>
        (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i)
  have hspan' :
      ZeroProfileProjectedCommonSpanWithBudget
        (Nat.log 2 (2 ^ 804) + 1)
        (fun i =>
          (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i =>
            (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i))
        (withinProfileBound (Nat.log 2 (2 ^ 804) + 1)) := hspan
  exact hiff.mp hspan'

/-- The canonical singleton-quotient zero-profile field is therefore equivalent
to the exact projected quotient budget bound. -/
theorem paperScaleSingletonQuotient_projectedZeroCommonSpan_iff_exactBudget_le
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PaperScaleCookLevinOneWindowProjectedZeroHistogramShiftCommonSpan
        M htb hns
        (paperScaleCookLevinSingletonQuotientProjection M htb hns) ↔
      zeroProfileSingletonQuotientProjectedTypeBudget
          (Nat.log 2 (2 ^ 804) + 1)
          (fun i =>
            (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i) ≤
        withinProfileBound (Nat.log 2 (2 ^ 804) + 1) := by
  constructor
  · exact exactBudget_le_of_paperScaleSingletonQuotient_projectedZeroCommonSpan
      M htb hns
  · exact paperScaleSingletonQuotient_projectedZeroCommonSpan_of_exactBudget_le
      M htb hns

/-- Named nontrivial singleton-quotient zero-profile payload.  This is the field
that should replace the weak arbitrary-projection socket in future payload
interfaces. -/
abbrev PaperScaleSingletonQuotientProjectedZeroProfileBudgetBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  zeroProfileSingletonQuotientProjectedTypeBudget
      (Nat.log 2 (2 ^ 804) + 1)
      (fun i =>
        (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i) ≤
    withinProfileBound (Nat.log 2 (2 ^ 804) + 1)

/-! ## Axiom audit anchors -/

#print axioms zeroProfileProjectedCommonSpanWithBudget_singletonQuotient_of_exactBudget_le
#print axioms zeroProfileProjectedCommonSpanWithBudget_singletonQuotient_iff_exactBudget_le
#print axioms paperScaleSingletonQuotient_projectedZeroCommonSpan_of_exactBudget_le
#print axioms exactBudget_le_of_paperScaleSingletonQuotient_projectedZeroCommonSpan
#print axioms paperScaleSingletonQuotient_projectedZeroCommonSpan_iff_exactBudget_le

end PallLean.Paper93.DeepMath.PathC
