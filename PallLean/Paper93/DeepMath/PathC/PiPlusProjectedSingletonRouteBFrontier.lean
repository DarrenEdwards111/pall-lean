import PallLean.Paper93.DeepMath.PathC.PiPlusSharpProjectedFinal
import PallLean.Paper93.DeepMath.PathC.PiPlusProjectedZeroSingletonSpan
import PallLean.Paper93.DeepMath.PathC.PiPlusOneWindowZeroContainmentObstruction

/-!
# Projected singleton-quotient Route-B frontier

This file pins the remaining corrected Route-B payload to the viable projected
singleton quotient, rather than the impossible unprojected/identity zero-profile
socket.

The zero-profile ingredient is now exactly the singleton-quotient type-budget
inequality.  The active-profile ingredient is the existing one-window active
local data.  What remains is no longer a zero-profile common-span theorem: it is
the direct source rank theorem `RouteBSATWindowedIncPSideRankBound` at the
one-window inclusive source polynomial.  This is the theorem that a genuinely
projected Route-B proof must establish without reintroducing the false identity
zero socket.
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

/-- The zero-profile singleton-quotient budget at paper scale.  This is the
correct replacement for the impossible unprojected zero common-span field. -/
def PaperScaleSingletonQuotientZeroProfileBudget
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  zeroProfileSingletonQuotientProjectedTypeBudget
      (Nat.log 2 (2 ^ 804) + 1)
      (fun i =>
        (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i) ≤
    withinProfileBound (Nat.log 2 (2 ^ 804) + 1)

/-- The direct projected Route-B bridge that remains after the singleton
quotient has replaced the dead unprojected zero socket.

This is deliberately stated as a source-rank theorem, because the downstream
Route-C final theorem consumes `RouteBSATWindowedIncPSideRankBound`; projected
zero-profile data alone cannot be coerced into the old unprojected
within-profile proof without contradicting
`not_paperScale_cookLevinOneWindowZeroProfilePostSpanContainment`. -/
def PaperScaleSingletonQuotientRouteBBridge
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (_hzero : PaperScaleSingletonQuotientZeroProfileBudget M htb hns)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ))
    (_W_finite : ∀ τ, Module.Finite ℚ ↥(W τ))
    (_W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (_active_data : CookLevinOneWindowPerTypeSpanningActiveData
      M (2 ^ 804) paperScale_ge_two htb hns W) : Prop :=
  RouteBSATWindowedIncPSideRankBound
    1 0 M (2 ^ 804) paperScale_ge_two htb hns

/-- Full paper-scale singleton-quotient frontier data, with the P-side and
NP-side sharp payloads separated from the corrected projected Route-B payload. -/
structure PaperScalePiPlusSingletonQuotientFinalFrontier
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Type where
  normalized_derivative_span :
    PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan M htb hns
  transformed_generator_rows :
    PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorRowCertificateOneZero
      M htb hns
  np_window_rows :
    PaperScalePiPlusBooleanProjectedNPWindowRowInclusion M htb hns
  zero_budget : PaperScaleSingletonQuotientZeroProfileBudget M htb hns
  W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ)
  W_finite : ∀ τ, Module.Finite ℚ ↥(W τ)
  W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3
  active_data : CookLevinOneWindowPerTypeSpanningActiveData
    M (2 ^ 804) paperScale_ge_two htb hns W
  routeB_bridge : PaperScaleSingletonQuotientRouteBBridge
    M htb hns zero_budget W W_finite W_dim active_data

/-- The singleton quotient frontier directly fills the final Route-C bridge.
The zero-budget and active-data fields are retained in the structure so the
remaining Route-B bridge cannot silently fall back to the impossible old zero
socket. -/
theorem no_decidesSAT_at_paperScale_of_singletonQuotientFinalFrontier
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusSingletonQuotientFinalFrontier M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_sharpPsidePayloads_npRow_projectedRouteB
    M htb hns
    D.normalized_derivative_span
    D.transformed_generator_rows
    D.np_window_rows
    D.routeB_bridge

/-! ## Axiom audit anchors -/

#print axioms no_decidesSAT_at_paperScale_of_singletonQuotientFinalFrontier

end PallLean.Paper93.DeepMath.PathC
