import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNPDerivativeCongruence

/-!
# Obstruction to naive Booleanity derivative erasure

The Booleanity-factor product is quotient-equal to `1`, but ordinary
partial derivatives do **not** respect that replacement.  Already for one
variable,

`∂(1 - X + X²) = -1 + 2X`,

which is nonzero in the Boolean ambient.  This file pins that obstruction in the
kernel so the Route-C NP closure does not proceed by the false derivative-level
claim that differentiated Booleanity factors can simply be erased.
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

/-- The Boolean-normal representative of `-1 + 2X` is not zero. -/
theorem liftToBool_neg_one_add_twoX_ne_zero :
    liftToBool (((-1 : MvPolynomial (Fin 1) ℚ) + C (2 : ℚ) * X 0)) ≠
      liftToBool (0 : MvPolynomial (Fin 1) ℚ) := by
  intro h
  have hc := congrArg
    (fun r : BoolPoly 1 =>
      coeff (Finsupp.single (0 : Fin 1) 1) (r : MvPolynomial (Fin 1) ℚ)) h
  have hnorm2 :
      zeroProfileBooleanNormalize ((C (2 : ℚ) : MvPolynomial (Fin 1) ℚ) * X 0) =
        (C (2 : ℚ) : MvPolynomial (Fin 1) ℚ) * X 0 := by
    rw [MvPolynomial.C_mul_X_eq_monomial]
    rw [zeroProfileBooleanNormalize_monomial]
    simp
  simp [liftToBool, zeroProfileBooleanNormalize_add,
    zeroProfileBooleanNormalize_neg, hnorm2] at hc
  have hone :
      coeff (Finsupp.single (0 : Fin 1) 1) (1 : MvPolynomial (Fin 1) ℚ) = 0 := by
    rw [MvPolynomial.coeff_one]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
    intro hz
    have hval := congrArg (fun f : Fin 1 →₀ ℕ => f (0 : Fin 1)) hz
    simp at hval
  rw [hone] at hc
  norm_num at hc

/-- One-variable counterexample to naive derivative-level erasure of Booleanity
factors.  With rest factor `1`, differentiating the Booleanity product does not
agree in the Boolean ambient with differentiating the erased rest factor. -/
theorem booleanityDerivativeErasure_oneVar_counterexample :
    liftToBool
        (iterDerivList [0]
          (cookLevinBooleanFactorProd 1 * (1 : MvPolynomial (Fin 1) ℚ))) ≠
      liftToBool
        (iterDerivList [0] (1 : MvPolynomial (Fin 1) ℚ)) := by
  rw [mul_one]
  unfold iterDerivList
  simp only [List.foldl_cons, List.foldl_nil]
  rw [cookLevinBooleanFactorProd_eq_finRange]
  simp [List.finRange]
  change liftToBool (pderiv (0 : Fin 1) (cookLevinBooleanFactor 1 0)) ≠
    liftToBool (0 : MvPolynomial (Fin 1) ℚ)
  rw [pderiv_cookLevinBooleanFactor_self]
  change liftToBool (((-1 : MvPolynomial (Fin 1) ℚ) + C (2 : ℚ) * X 0)) ≠
    liftToBool (0 : MvPolynomial (Fin 1) ℚ)
  exact liftToBool_neg_one_add_twoX_ne_zero

/-! ## Axiom audit anchors -/

#print axioms liftToBool_neg_one_add_twoX_ne_zero
#print axioms booleanityDerivativeErasure_oneVar_counterexample

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
