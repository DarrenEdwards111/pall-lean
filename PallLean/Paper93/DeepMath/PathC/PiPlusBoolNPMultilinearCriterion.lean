import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNPNormalityCriterion

/-!
# Multilinearity criterion for Boolean NP normality

The previous layer named the clean normal-form seam:
`zeroProfileBooleanNormalize compiledPoly = compiledPoly`.  This file gives the
standard sufficient condition: support-wise multilinearity.  Thus, if the
Cook--Levin compiled polynomial is multilinear, the Boolean normality seam
closes immediately.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

namespace BoolPoly

/-- Multilinear full-ring polynomials are fixed by Boolean normalization. -/
theorem booleanNormal_of_isMultilinear {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) (hp : IsMultilinear p) :
    IsBooleanNormal p := by
  unfold IsBooleanNormal
  exact zeroProfileBooleanNormalize_of_support_isMultilinear p hp

/-- Boolean-normality criterion for Cook--Levin at paper scale: the compiled
polynomial is multilinear in the full-ring sense. -/
def PaperScaleCookLevinCompiledIsMultilinear
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  IsMultilinear
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale multilinearity closes the Boolean-normality seam. -/
theorem paperScaleCookLevinCompiledBooleanNormal_of_isMultilinear
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hml : PaperScaleCookLevinCompiledIsMultilinear M htb hns) :
    PaperScaleCookLevinCompiledBooleanNormal M htb hns := by
  unfold PaperScaleCookLevinCompiledIsMultilinear
    PaperScaleCookLevinCompiledBooleanNormal at *
  exact booleanNormal_of_isMultilinear
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hml

/-- Final no-decider surface where NP image exactness is supplied by
multilinearity of the compiled polynomial. -/
theorem no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPMultilinearKernelFromDecider
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HrowInc : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservationInc M htb hns)
    (Hrow : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservation M htb hns)
    (HP : DecidesSAT M → PaperScaleCookLevinLegacyBlockedIncPSideRankBoundOneZero M htb hns)
    (Hml : DecidesSAT M → PaperScaleCookLevinCompiledIsMultilinear M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M := by
  apply no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPNormalKernelFromDecider
    M htb hns HrowInc Hrow HP
  · intro hdec
    exact paperScaleCookLevinCompiledBooleanNormal_of_isMultilinear
      M htb hns (Hml hdec)
  · exact Hker

/-! ## Axiom audit anchors -/

#print axioms booleanNormal_of_isMultilinear
#print axioms paperScaleCookLevinCompiledBooleanNormal_of_isMultilinear
#print axioms no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPMultilinearKernelFromDecider

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
