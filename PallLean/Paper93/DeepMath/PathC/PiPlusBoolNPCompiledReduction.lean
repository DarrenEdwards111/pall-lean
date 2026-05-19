import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNPMultilinearCriterion

/-!
# Boolean quotient reduction of the compiled Cook--Levin polynomial

The full Cook--Levin compiled polynomial is not expected to be multilinear: its
Booleanity factors are `1 - Xᵢ(1-Xᵢ) = 1 - Xᵢ + Xᵢ²`.  The paper's Boolean
ambient therefore should not try to prove raw full-ring normality of the whole
compiled polynomial.

This file records the correct quotient statement: Boolean normalization erases
the exposed Booleanity-factor product and leaves the adjacency/transition rest
factor.
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

/-- In the Boolean quotient, the Cook--Levin compiled polynomial reduces to the
rest factor product: Booleanity factors are quotient-units normalized to `1`. -/
theorem zeroProfileBooleanNormalize_compiledPoly_eq_restFactor
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    zeroProfileBooleanNormalize
      (compiledPoly (cook_levin_compilation M n hn htb hns)) =
    zeroProfileBooleanNormalize (restFactorProd' M n) := by
  rw [compiledPoly_factored M n hn htb hns]
  change zeroProfileBooleanNormalize (cookLevinBooleanFactorProd n * restFactorProd' M n) =
    zeroProfileBooleanNormalize (restFactorProd' M n)
  exact zeroProfileBooleanNormalize_cookLevinBooleanFactorProd_mul n (restFactorProd' M n)

/-- Paper-scale specialization of the quotient reduction. -/
theorem paperScale_zeroProfileBooleanNormalize_compiledPoly_eq_restFactor
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    zeroProfileBooleanNormalize
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)) =
    zeroProfileBooleanNormalize (restFactorProd' M (2 ^ 804)) :=
  zeroProfileBooleanNormalize_compiledPoly_eq_restFactor
    M (2 ^ 804) paperScale_ge_two htb hns

/-- The full-ring representative of the Boolean image of the compiled polynomial
is the normalized rest factor, not generally the raw compiled polynomial. -/
theorem paperScale_compiled_liftToBool_coe_eq_normalizedRest
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    (((liftToBool
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)) :
        BoolPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) :
          MvPolynomial
            (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ)) =
    zeroProfileBooleanNormalize (restFactorProd' M (2 ^ 804)) := by
  change zeroProfileBooleanNormalize
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)) =
    zeroProfileBooleanNormalize (restFactorProd' M (2 ^ 804))
  exact paperScale_zeroProfileBooleanNormalize_compiledPoly_eq_restFactor M htb hns

/-! ## Axiom audit anchors -/

#print axioms zeroProfileBooleanNormalize_compiledPoly_eq_restFactor
#print axioms paperScale_zeroProfileBooleanNormalize_compiledPoly_eq_restFactor
#print axioms paperScale_compiled_liftToBool_coe_eq_normalizedRest

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
