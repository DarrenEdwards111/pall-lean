import PallLean.Paper93.DeepMath.PathC.PiPlusProjectedSingletonRouteBFrontier
import PallLean.Paper93.DeepMath.PathB.ZeroProfileFiniteNormalFormClassifier

/-!
# One-window finite-normal-form route to the singleton quotient budget

`ZeroProfileFiniteNormalFormClassifier` already proves the zero-profile
singleton-quotient budget at the hardcoded `log n` radius.  Route C needs the
same paper-faithful normal-form interface at the enlarged one-window radius
`log n + 1`.

This file adds that one-window specialization without using the false identity
zero-profile containment.
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

/-- Generic one-window singleton-quotient budget from a finite normal-form row
classifier at the enlarged radius `log₂ n + 1`. -/
theorem zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_oneWindow_of_finiteNormalFormClassifier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget : ℕ}
    {A : ZeroProfileFiniteNormalFormAlphabet (Nat.log 2 n + 1)}
    (D : ZeroProfileFiniteNormalFormFamilyData A n typeBudget)
    (C :
      ZeroProfileFiniteNormalFormRowClassifier
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn htb hns).get i))
        D)
    (hbudget : typeBudget ≤ withinProfileBound (Nat.log 2 n + 1)) :
    zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n + 1)
        (fun i => (cookLevinFactorList M n hn htb hns).get i) ≤
      withinProfileBound (Nat.log 2 n + 1) := by
  have hcommon :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n + 1)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn htb hns).get i))
        typeBudget :=
    zeroProfileProjectedCommonSpanWithBudget_of_finiteNormalFormClassifier
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn htb hns).get i))
      D C
  exact
    (zeroProfileSingletonQuotientProjectedTypeBudget_le_of_projectedCommonSpan
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      hcommon).trans hbudget

/-- Paper-scale one-window singleton-quotient zero-budget from a finite
normal-form classifier. -/
theorem paperScaleSingletonQuotientZeroProfileBudget_of_finiteNormalFormClassifier
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    {typeBudget : ℕ}
    {A : ZeroProfileFiniteNormalFormAlphabet (Nat.log 2 (2 ^ 804) + 1)}
    (D : ZeroProfileFiniteNormalFormFamilyData A (2 ^ 804) typeBudget)
    (C :
      ZeroProfileFiniteNormalFormRowClassifier
        (fun i =>
          (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i =>
            (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i))
        D)
    (hbudget : typeBudget ≤ withinProfileBound (Nat.log 2 (2 ^ 804) + 1)) :
    PaperScaleSingletonQuotientZeroProfileBudget M htb hns :=
  zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_oneWindow_of_finiteNormalFormClassifier
    M (2 ^ 804) paperScale_ge_two htb hns D C hbudget

/-- Final frontier constructor where the zero-profile budget is supplied by the
one-window finite normal-form classifier. -/
def singletonQuotientFinalFrontier_of_finiteNormalFormClassifier
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan M htb hns)
    (hcert : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneZero
      M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowRowInclusion M htb hns)
    {typeBudget : ℕ}
    {A : ZeroProfileFiniteNormalFormAlphabet (Nat.log 2 (2 ^ 804) + 1)}
    (Dnf : ZeroProfileFiniteNormalFormFamilyData A (2 ^ 804) typeBudget)
    (Cnf :
      ZeroProfileFiniteNormalFormRowClassifier
        (fun i =>
          (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i =>
            (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i))
        Dnf)
    (hnfBudget : typeBudget ≤ withinProfileBound (Nat.log 2 (2 ^ 804) + 1))
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ))
    (W_finite : ∀ τ, Module.Finite ℚ ↥(W τ))
    (W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (active_data : CookLevinOneWindowPerTypeSpanningActiveData
      M (2 ^ 804) paperScale_ge_two htb hns W)
    (routeB_bridge : PaperScaleSingletonQuotientRouteBBridge
      M htb hns
      (paperScaleSingletonQuotientZeroProfileBudget_of_finiteNormalFormClassifier
        M htb hns Dnf Cnf hnfBudget)
      W W_finite W_dim active_data) :
    PaperScalePiPlusSingletonQuotientFinalFrontier M htb hns where
  normalized_derivative_span := hpoly
  transformed_generator_rows := hcert
  np_window_rows := hnp
  zero_budget :=
    paperScaleSingletonQuotientZeroProfileBudget_of_finiteNormalFormClassifier
      M htb hns Dnf Cnf hnfBudget
  W := W
  W_finite := W_finite
  W_dim := W_dim
  active_data := active_data
  routeB_bridge := routeB_bridge

/-! ## Axiom audit anchors -/

#print axioms zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_oneWindow_of_finiteNormalFormClassifier
#print axioms paperScaleSingletonQuotientZeroProfileBudget_of_finiteNormalFormClassifier
#print axioms singletonQuotientFinalFrontier_of_finiteNormalFormClassifier

end PallLean.Paper93.DeepMath.PathC
