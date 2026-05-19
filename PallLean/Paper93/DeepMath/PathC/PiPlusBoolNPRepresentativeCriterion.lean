import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNPDerivativeNormalizeCriterion

/-!
# Representative criterion for Boolean NP derivative normalization

The previous layer reduces NP image exactness to row-wise derivative-normalization
compatibility between the raw compiled polynomial and its Boolean-normal
representative.  This file records the simplest sufficient condition: the raw
compiled polynomial is already represented by the Boolean-normal polynomial.

This is intentionally strong.  If it fails for the Cook--Levin product, the next
mathematical move is not to hide it, but to replace this file's sufficient
criterion with a genuine Boolean-derivative/product theorem.
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

/-- If the raw polynomial and the Boolean representative are definitionally the
same full-ring polynomial, then the derivative-normalization row criterion is
immediate. -/
theorem rawToBoolDerivativeNormalizationRows_of_representative_eq {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (q : MvPolynomial (Fin n) ℚ) (p : BoolPoly n)
    (hrep : q = (p : MvPolynomial (Fin n) ℚ)) :
    RawToBoolDerivativeNormalizationRows B κ ℓ q p := by
  intro S m _hlen _hdeg _hvars _hadm
  subst hrep
  rfl

/-- Paper-scale representative-exactness criterion: the raw Cook--Levin compiled
polynomial is already its Boolean-normal representative. -/
def PaperScaleCookLevinCompiledBoolRepresentativeExact
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns) =
    ((paperScaleCompiledBoolPoly M htb hns) :
      MvPolynomial
        (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ)

/-- Representative exactness gives the paper-scale derivative-normalization row
criterion. -/
theorem paperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows_of_representativeExact
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrep : PaperScaleCookLevinCompiledBoolRepresentativeExact M htb hns) :
    PaperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows M htb hns := by
  unfold PaperScaleCookLevinCompiledBoolRepresentativeExact
    PaperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows at *
  exact rawToBoolDerivativeNormalizationRows_of_representative_eq
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    (paperScaleCompiledBoolPoly M htb hns)
    hrep

/-- Final no-decider surface where NP image exactness is supplied by the strong
representative-exactness criterion. -/
theorem no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPRepresentativeKernelFromDecider
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HrowInc : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservationInc M htb hns)
    (Hrow : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservation M htb hns)
    (HP : DecidesSAT M → PaperScaleCookLevinLegacyBlockedIncPSideRankBoundOneZero M htb hns)
    (Hrep : DecidesSAT M → PaperScaleCookLevinCompiledBoolRepresentativeExact M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M := by
  apply no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPDerivativeRowsKernelFromDecider
    M htb hns HrowInc Hrow HP
  · intro hdec
    exact paperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows_of_representativeExact
      M htb hns (Hrep hdec)
  · exact Hker

/-! ## Axiom audit anchors -/

#print axioms rawToBoolDerivativeNormalizationRows_of_representative_eq
#print axioms paperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows_of_representativeExact
#print axioms no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPRepresentativeKernelFromDecider

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
