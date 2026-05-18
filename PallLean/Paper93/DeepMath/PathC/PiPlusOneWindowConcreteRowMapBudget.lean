import PallLean.Paper93.DeepMath.PathC.PiPlusOneWindowFiniteNormalFormBudget

/-!
# One-window concrete row-map route to the singleton quotient budget

This narrows the zero-profile obligation below the finite-normal-form
classifier layer.  It says that it is enough to build the concrete row map into
the actual singleton zero-profile `concreteW` chart at radius `log n + 1`, using
the singleton-quotient projection.

This is strictly weaker than the false identity containment: the rows are first
projected by the singleton quotient, so the singleton-shift obstruction is
removed before asking for membership in the concrete zero-profile chart.
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

/-- Concrete one-window singleton-quotient row-map target.  This is the current
sharp zero-profile local theorem: after applying the singleton quotient
projection, every one-window zero-profile shifted Cook--Levin row lands in the
singleton zero-profile concrete `concreteW` chart. -/
abbrev CookLevinOneWindowSingletonQuotientConcreteRowMap
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4) : Type :=
  ZeroProfileConcreteNormalFormRowMap
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (zeroProfileQuotientBySingletonShiftProjection
      (fun i => (cookLevinFactorList M n hn htb hns).get i))
    (zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW
      (κ := Nat.log 2 n + 1) hn4)

/-- A concrete singleton-quotient row map gives the one-window singleton-quotient
zero-profile budget. -/
theorem zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_oneWindow_of_concreteRowMap
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hmap : CookLevinOneWindowSingletonQuotientConcreteRowMap
      M n hn htb hns hn4) :
    zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n + 1)
        (fun i => (cookLevinFactorList M n hn htb hns).get i) ≤
      withinProfileBound (Nat.log 2 n + 1) := by
  exact
    zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_oneWindow_of_finiteNormalFormClassifier
      M n hn htb hns
      (zeroProfileFiniteNormalFormFamilyData_of_concreteData
        (zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW
          (κ := Nat.log 2 n + 1) hn4))
      (zeroProfileFiniteNormalFormRowClassifier_of_concreteRowMap
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn htb hns).get i))
        (zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW
          (κ := Nat.log 2 n + 1) hn4)
        hmap)
      (zeroProfileSymmetricProfileDim_zeroProfileHistogram_le_withinProfileBound
        (Nat.log 2 n + 1))

/-- Paper-scale version of the concrete singleton-quotient row-map budget
bridge. -/
theorem paperScaleSingletonQuotientZeroProfileBudget_of_concreteRowMap
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hmap : CookLevinOneWindowSingletonQuotientConcreteRowMap
      M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four) :
    PaperScaleSingletonQuotientZeroProfileBudget M htb hns :=
  zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_oneWindow_of_concreteRowMap
    M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four hmap

/-- Final frontier constructor where the zero-profile budget is supplied by the
concrete singleton-quotient row map. -/
def singletonQuotientFinalFrontier_of_concreteRowMap
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan M htb hns)
    (hcert : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneZero
      M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowRowInclusion M htb hns)
    (hmap : CookLevinOneWindowSingletonQuotientConcreteRowMap
      M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ))
    (W_finite : ∀ τ, Module.Finite ℚ ↥(W τ))
    (W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (active_data : CookLevinOneWindowPerTypeSpanningActiveData
      M (2 ^ 804) paperScale_ge_two htb hns W)
    (routeB_bridge : PaperScaleSingletonQuotientRouteBBridge
      M htb hns
      (paperScaleSingletonQuotientZeroProfileBudget_of_concreteRowMap
        M htb hns hmap)
      W W_finite W_dim active_data) :
    PaperScalePiPlusSingletonQuotientFinalFrontier M htb hns where
  normalized_derivative_span := hpoly
  transformed_generator_rows := hcert
  np_window_rows := hnp
  zero_budget := paperScaleSingletonQuotientZeroProfileBudget_of_concreteRowMap
    M htb hns hmap
  W := W
  W_finite := W_finite
  W_dim := W_dim
  active_data := active_data
  routeB_bridge := routeB_bridge

/-! ## Axiom audit anchors -/

#print axioms zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_oneWindow_of_concreteRowMap
#print axioms paperScaleSingletonQuotientZeroProfileBudget_of_concreteRowMap
#print axioms singletonQuotientFinalFrontier_of_concreteRowMap

end PallLean.Paper93.DeepMath.PathC
