import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNPFactoredRestSplit

/-!
# Row-multiplication congruence for Boolean NP derivative seams

The split factored-rest obligations still quantify over the row multiplier `m`.
This file removes that nuisance: equality in the Boolean ambient is stable under
left multiplication by any row multiplier.  Consequently the two row-level NP
payloads reduce to derivative-level Boolean equalities.
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

/-- Boolean equality is a congruence for left multiplication in the raw ring
followed by `liftToBool`. -/
theorem liftToBool_mul_right_congr {n : ℕ}
    (m a b : MvPolynomial (Fin n) ℚ)
    (h : liftToBool a = liftToBool b) :
    liftToBool (m * a) = liftToBool (m * b) := by
  apply BoolPoly.ext
  change zeroProfileBooleanNormalize (m * a) = zeroProfileBooleanNormalize (m * b)
  have hnorm : zeroProfileBooleanNormalize a = zeroProfileBooleanNormalize b := by
    simpa using congrArg (fun r : BoolPoly n => (r : MvPolynomial (Fin n) ℚ)) h
  calc
    zeroProfileBooleanNormalize (m * a) =
        zeroProfileBooleanNormalize (m * zeroProfileBooleanNormalize a) := by
          exact (zeroProfileBooleanNormalize_mul_right_normalized m a).symm
    _ = zeroProfileBooleanNormalize (m * zeroProfileBooleanNormalize b) := by
          rw [hnorm]
    _ = zeroProfileBooleanNormalize (m * b) := by
          exact zeroProfileBooleanNormalize_mul_right_normalized m b

/-- Derivative-level Booleanity-erasure: differentiated rows agree before the
SPDP row multiplier is applied. -/
def PaperScaleCookLevinBooleanityDerivativeErasure
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  ∀ (S : List (Fin (2 ^ 804))),
    S.length = Nat.log 2 (2 ^ 804) →
    isBlockAdmissible
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition S →
      liftToBool
        (iterDerivList S
          (cookLevinBooleanFactorProd (2 ^ 804) * restFactorProd' M (2 ^ 804))) =
      liftToBool
        (iterDerivList S (restFactorProd' M (2 ^ 804)))

/-- Derivative-level rest normalization: rest derivatives agree with derivatives
of the Boolean-normal rest representative before row multiplication. -/
def PaperScaleCookLevinRestDerivativeNormalization
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  ∀ (S : List (Fin (2 ^ 804))),
    S.length = Nat.log 2 (2 ^ 804) →
    isBlockAdmissible
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition S →
      liftToBool
        (iterDerivList S (restFactorProd' M (2 ^ 804))) =
      liftToBool
        (iterDerivList S
          (zeroProfileBooleanNormalize (restFactorProd' M (2 ^ 804))))

/-- Derivative-level Booleanity erasure implies the row-level erasure payload. -/
theorem paperScaleCookLevinBooleanityDerivativeErasureRows_of_derivativeErasure
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (herase : PaperScaleCookLevinBooleanityDerivativeErasure M htb hns) :
    PaperScaleCookLevinBooleanityDerivativeErasureRows M htb hns := by
  intro S m hlen _hdeg _hvars hadm
  exact liftToBool_mul_right_congr m
    (iterDerivList S
      (cookLevinBooleanFactorProd (2 ^ 804) * restFactorProd' M (2 ^ 804)))
    (iterDerivList S (restFactorProd' M (2 ^ 804)))
    (herase S hlen hadm)

/-- Derivative-level rest normalization implies the row-level rest-normalization
payload. -/
theorem paperScaleCookLevinRestDerivativeNormalizationRows_of_derivativeNormalization
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrest : PaperScaleCookLevinRestDerivativeNormalization M htb hns) :
    PaperScaleCookLevinRestDerivativeNormalizationRows M htb hns := by
  intro S m hlen _hdeg _hvars hadm
  exact liftToBool_mul_right_congr m
    (iterDerivList S (restFactorProd' M (2 ^ 804)))
    (iterDerivList S
      (zeroProfileBooleanNormalize (restFactorProd' M (2 ^ 804))))
    (hrest S hlen hadm)

/-- Final no-decider surface with NP derivative seams reduced to derivative-level
Boolean equalities, no row multiplier. -/
theorem no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPDerivativeCongruenceKernelFromDecider
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HrowInc : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservationInc M htb hns)
    (Hrow : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservation M htb hns)
    (HP : DecidesSAT M → PaperScaleCookLevinLegacyBlockedIncPSideRankBoundOneZero M htb hns)
    (Herase : DecidesSAT M → PaperScaleCookLevinBooleanityDerivativeErasure M htb hns)
    (Hrest : DecidesSAT M → PaperScaleCookLevinRestDerivativeNormalization M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M := by
  apply no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPSplitFactoredRestKernelFromDecider
    M htb hns HrowInc Hrow HP
  · intro hdec
    exact paperScaleCookLevinBooleanityDerivativeErasureRows_of_derivativeErasure
      M htb hns (Herase hdec)
  · intro hdec
    exact paperScaleCookLevinRestDerivativeNormalizationRows_of_derivativeNormalization
      M htb hns (Hrest hdec)
  · exact Hker

/-! ## Axiom audit anchors -/

#print axioms liftToBool_mul_right_congr
#print axioms paperScaleCookLevinBooleanityDerivativeErasureRows_of_derivativeErasure
#print axioms paperScaleCookLevinRestDerivativeNormalizationRows_of_derivativeNormalization
#print axioms no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPDerivativeCongruenceKernelFromDecider

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
