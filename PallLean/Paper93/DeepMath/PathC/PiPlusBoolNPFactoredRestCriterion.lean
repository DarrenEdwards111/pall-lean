import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNPCompiledReduction

/-!
# Factored-rest criterion for Boolean NP derivative rows

The quotient-level polynomial identity is

`normalize compiledPoly = normalize restFactorProd'`,

because the exposed Booleanity-factor product normalizes to `1`.  Derivatives do
not automatically respect quotient representatives, so the remaining NP image
seam must be stated at the row level.

This file replaces the too-strong representative/normality route with the honest
row target:

`liftToBool (m * ∂_S (booleanityProduct * rest)) =
 liftToBool (m * ∂_S (normalize rest))`.

That is the exact algebraic payload needed to close paper-scale NP derivative
normalization after the compiled polynomial has been factored.
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

/-- Row-wise quotient-correct derivative compatibility for the factored
Cook--Levin source polynomial.  The RHS differentiates the normalized rest
representative, not the raw compiled polynomial. -/
def PaperScaleCookLevinFactoredToNormalizedRestDerivativeRows
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
        (m * iterDerivList S
          (zeroProfileBooleanNormalize (restFactorProd' M (2 ^ 804))))

/-- The factored-rest derivative row criterion implies the existing paper-scale
raw-to-Boolean derivative-normalization rows. -/
theorem paperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows_of_factoredRestRows
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrows : PaperScaleCookLevinFactoredToNormalizedRestDerivativeRows M htb hns) :
    PaperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows M htb hns := by
  unfold PaperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows
  intro S m hlen hdeg hvars hadm
  have hfact := compiledPoly_factored M (2 ^ 804) paperScale_ge_two htb hns
  have hp :
      (((paperScaleCompiledBoolPoly M htb hns) :
        MvPolynomial
          (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ)) =
        zeroProfileBooleanNormalize (restFactorProd' M (2 ^ 804)) := by
    exact paperScale_compiled_liftToBool_coe_eq_normalizedRest M htb hns
  change liftToBool
      (m * iterDerivList S
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))) =
    liftToBool
      (m * iterDerivList S
        (((paperScaleCompiledBoolPoly M htb hns) :
          MvPolynomial
            (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ)))
  rw [hfact, hp]
  exact hrows S m hlen hdeg hvars hadm

/-- Final no-decider surface using the quotient-correct factored-rest derivative
row seam plus kernel disjointness. -/
theorem no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPFactoredRestKernelFromDecider
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HrowInc : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservationInc M htb hns)
    (Hrow : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservation M htb hns)
    (HP : DecidesSAT M → PaperScaleCookLevinLegacyBlockedIncPSideRankBoundOneZero M htb hns)
    (HfactRows : DecidesSAT M → PaperScaleCookLevinFactoredToNormalizedRestDerivativeRows M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M := by
  apply no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPDerivativeRowsKernelFromDecider
    M htb hns HrowInc Hrow HP
  · intro hdec
    exact paperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows_of_factoredRestRows
      M htb hns (HfactRows hdec)
  · exact Hker

/-! ## Axiom audit anchors -/

#print axioms paperScaleCookLevinRawToBoolSourceNPDerivativeNormalizationRows_of_factoredRestRows
#print axioms no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPFactoredRestKernelFromDecider

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
