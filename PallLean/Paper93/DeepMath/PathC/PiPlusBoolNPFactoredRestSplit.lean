import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNPFactoredRestCriterion

/-!
# Split the factored-rest NP derivative row seam

`PiPlusBoolNPFactoredRestCriterion` isolates the quotient-correct target:
rows of the factored Cook--Levin product must agree in `BoolPoly` with rows of
the normalized rest representative.

This file splits that target into two sharper obligations:

1. differentiated Booleanity factors are invisible in the Boolean ambient;
2. derivatives of the rest factor commute with replacing the rest factor by its
   Boolean-normal representative.

Together they imply the existing factored-rest row criterion and hence feed the
same final no-decider bridge.
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

/-- First payload: after multiplying by the admissible row monomial `m`, the
Booleanity-factor part of the factored Cook--Levin derivative is invisible in the
Boolean ambient. -/
def PaperScaleCookLevinBooleanityDerivativeErasureRows
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  ∀ (S : List (Fin (2 ^ 804))) (m : MvPolynomial (Fin (2 ^ 804)) ℚ),
    S.length = Nat.log 2 (2 ^ 804) →
    m.totalDegree ≤ Nat.log 2 (2 ^ 804) →
    m.vars ⊆ S.toFinset →
    isBlockAdmissible
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition S →
      liftToBool
        (m * iterDerivList S
          (cookLevinBooleanFactorProd (2 ^ 804) * restFactorProd' M (2 ^ 804))) =
      liftToBool
        (m * iterDerivList S (restFactorProd' M (2 ^ 804)))

/-- Second payload: the rest-factor rows are unchanged in the Boolean ambient
when the rest factor is replaced by its Boolean-normal representative. -/
def PaperScaleCookLevinRestDerivativeNormalizationRows
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  ∀ (S : List (Fin (2 ^ 804))) (m : MvPolynomial (Fin (2 ^ 804)) ℚ),
    S.length = Nat.log 2 (2 ^ 804) →
    m.totalDegree ≤ Nat.log 2 (2 ^ 804) →
    m.vars ⊆ S.toFinset →
    isBlockAdmissible
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition S →
      liftToBool
        (m * iterDerivList S (restFactorProd' M (2 ^ 804))) =
      liftToBool
        (m * iterDerivList S
          (zeroProfileBooleanNormalize (restFactorProd' M (2 ^ 804))))

/-- The two split payloads imply the quotient-correct factored-rest row seam. -/
theorem paperScaleCookLevinFactoredToNormalizedRestDerivativeRows_of_split
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (herase : PaperScaleCookLevinBooleanityDerivativeErasureRows M htb hns)
    (hrest : PaperScaleCookLevinRestDerivativeNormalizationRows M htb hns) :
    PaperScaleCookLevinFactoredToNormalizedRestDerivativeRows M htb hns := by
  intro S m hlen hdeg hvars hadm
  calc
    liftToBool
        (m * iterDerivList S
          (cookLevinBooleanFactorProd (2 ^ 804) * restFactorProd' M (2 ^ 804))) =
      liftToBool
        (m * iterDerivList S (restFactorProd' M (2 ^ 804))) :=
        herase S m hlen hdeg hvars hadm
    _ = liftToBool
        (m * iterDerivList S
          (zeroProfileBooleanNormalize (restFactorProd' M (2 ^ 804)))) :=
        hrest S m hlen hdeg hvars hadm

/-- The split payloads imply the existing raw-to-Boolean derivative-normalization
rows. -/
theorem paperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows_of_splitFactoredRest
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (herase : PaperScaleCookLevinBooleanityDerivativeErasureRows M htb hns)
    (hrest : PaperScaleCookLevinRestDerivativeNormalizationRows M htb hns) :
    PaperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows M htb hns :=
  paperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows_of_factoredRestRows
    M htb hns
    (paperScaleCookLevinFactoredToNormalizedRestDerivativeRows_of_split
      M htb hns herase hrest)

/-- Final no-decider surface with the NP derivative seam split into Booleanity
row erasure plus rest-row normalization. -/
theorem no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPSplitFactoredRestKernelFromDecider
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HrowInc : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservationInc M htb hns)
    (Hrow : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservation M htb hns)
    (HP : DecidesSAT M → PaperScaleCookLevinLegacyBlockedIncPSideRankBoundOneZero M htb hns)
    (Herase : DecidesSAT M → PaperScaleCookLevinBooleanityDerivativeErasureRows M htb hns)
    (Hrest : DecidesSAT M → PaperScaleCookLevinRestDerivativeNormalizationRows M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M := by
  apply no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPFactoredRestKernelFromDecider
    M htb hns HrowInc Hrow HP
  · intro hdec
    exact paperScaleCookLevinFactoredToNormalizedRestDerivativeRows_of_split
      M htb hns (Herase hdec) (Hrest hdec)
  · exact Hker

/-! ## Axiom audit anchors -/

#print axioms paperScaleCookLevinFactoredToNormalizedRestDerivativeRows_of_split
#print axioms paperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows_of_splitFactoredRest
#print axioms no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPSplitFactoredRestKernelFromDecider

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
