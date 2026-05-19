import PallLean.Paper93.DeepMath.PathC.PiPlusRawCompiledAgreementReduction
import PallLean.Paper93.DeepMath.PathC.PiPlusTransformedConstraintLeibniz

/-!
# Public projected fixedness to transformed product fixedness

The raw fixedness socket is deliberately stated using
`zeroProfileBooleanNormalize (Pi+(compiledPoly))`.  Lean expands that huge
paper-scale term aggressively if we try to rewrite it directly.

This file therefore records the next seam at the public Boolean-projected linear
map surface first: `cookLevinPiPlusBooleanProjectedGauge_paperScale compiledPoly`.
The concrete transport lemma already identifies that public surface with the
product of transformed local Cook--Levin factors.  A later lightweight bridge can
connect this public surface back to the raw fixedness socket without also
unfolding the product.
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

/-- Public-surface projected fixedness of the paper-scale compiled polynomial. -/
def PaperScaleCookLevinPiPlusPublicProjectedCompiledFixed
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)) =
    zeroProfileBooleanNormalize
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Product fixedness for the paper-scale transformed Cook--Levin local
constraint factors. -/
def PaperScaleCookLevinPiPlusTransformedConstraintProductFixed
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  zeroProfileBooleanNormalize
      (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).prod =
    zeroProfileBooleanNormalize
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- The concrete transport theorem reduces public projected compiled fixedness
to fixedness of the transformed local-factor product. -/
theorem paperScaleCookLevinPiPlusPublicProjectedCompiledFixed_of_transformedConstraintProductFixed
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hprod : PaperScaleCookLevinPiPlusTransformedConstraintProductFixed M htb hns) :
    PaperScaleCookLevinPiPlusPublicProjectedCompiledFixed M htb hns := by
  unfold PaperScaleCookLevinPiPlusPublicProjectedCompiledFixed
  exact Eq.trans
    (cookLevinPiPlusBooleanProjectedGauge_paperScale_compiledPoly_constraints M htb hns)
    hprod

/-- Decider-indexed version of the public product-reduction socket. -/
def PaperScaleCookLevinPiPlusPublicProjectedCompiledFixedFromProduct
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  DecidesSAT M → PaperScaleCookLevinPiPlusPublicProjectedCompiledFixed M htb hns

/-- Product fixedness gives the decider-indexed public projected fixedness
socket. -/
theorem paperScaleCookLevinPiPlusPublicProjectedCompiledFixedFromProduct_of_transformedConstraintProductFixed
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hprod : DecidesSAT M → PaperScaleCookLevinPiPlusTransformedConstraintProductFixed M htb hns) :
    PaperScaleCookLevinPiPlusPublicProjectedCompiledFixedFromProduct M htb hns := by
  intro hdec
  exact paperScaleCookLevinPiPlusPublicProjectedCompiledFixed_of_transformedConstraintProductFixed
    M htb hns (hprod hdec)

/-! ## Axiom audit anchors -/

#print axioms paperScaleCookLevinPiPlusPublicProjectedCompiledFixed_of_transformedConstraintProductFixed
#print axioms paperScaleCookLevinPiPlusPublicProjectedCompiledFixedFromProduct_of_transformedConstraintProductFixed

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
