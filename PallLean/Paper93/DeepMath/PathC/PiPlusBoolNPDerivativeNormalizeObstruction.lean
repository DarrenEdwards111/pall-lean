import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNPDerivativeNormalizeCriterion
import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNPDerivativeErasureObstruction

/-!
# Obstruction to unconditional derivative-normalization rows

`PiPlusBoolNPDerivativeNormalizeCriterion` reduces image exactness to a row-wise
compatibility between raw derivatives and derivatives of the Boolean-normal
representative.  This file proves that compatibility is not a free quotient law:
already the one-variable Booleanity factor violates it.
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

/-- The derivative-normalization criterion is not an unconditional Booleanity
factor erasure theorem.  Already in the one-variable Booleanity product, the
ordinary derivative of the raw representative survives in the Boolean ambient,
while the derivative of its normal representative `1` vanishes. -/
theorem not_rawToBoolDerivativeNormalizationRows_oneVar_booleanity
    (B : BlockPartition 1)
    (hadm : isBlockAdmissible B [(0 : Fin 1)]) :
    ¬ RawToBoolDerivativeNormalizationRows B 1 0
        (cookLevinBooleanFactorProd 1)
        (liftToBool (cookLevinBooleanFactorProd 1)) := by
  intro hrows
  have hrow := hrows [(0 : Fin 1)] (1 : MvPolynomial (Fin 1) ℚ)
    (by simp) (by simp) (by simp) hadm
  have hbad :
      liftToBool
          (iterDerivList [0]
            (cookLevinBooleanFactorProd 1 * (1 : MvPolynomial (Fin 1) ℚ))) =
        liftToBool
          (iterDerivList [0] (1 : MvPolynomial (Fin 1) ℚ)) := by
    simpa [one_mul, mul_one, zeroProfileBooleanNormalize_cookLevinBooleanFactorProd]
      using hrow
  exact booleanityDerivativeErasure_oneVar_counterexample hbad

/-! ## Axiom audit anchors -/

#print axioms not_rawToBoolDerivativeNormalizationRows_oneVar_booleanity

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
