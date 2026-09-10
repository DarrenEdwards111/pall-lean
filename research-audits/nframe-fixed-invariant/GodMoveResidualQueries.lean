import GodMoveRationalClearing
import Mathlib.Data.Nat.Size

/-!
# Explicit rational relations for the numeric residual test

The residual operation of the rational row basis is a linear map. Applying
it to the coordinate unit vectors computes an explicit coefficient row for
each residual coordinate. Thus a Boolean wire row lies outside the current
span exactly when one of these finitely many rational wire relations is
nonzero.

The bit-width function computes a sufficient numerator/denominator budget
from the actual supplied coefficients. This removes the need to supply a
precision witness separately. It does not bound the growth of those
coefficients across adaptive basis updates by a polynomial.
-/

namespace GodMoveResidualQueries

open GodMoveBooleanInterpolation GodMoveBooleanWireTable GodMoveRationalRowBasis
open GodMoveRowSpanSeparation GodMoveRationalClearing
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer (CGate runFrom)
open scoped BigOperators

/-- The actual rational orthogonal-residual operation, as a linear map. -/
def residualLinearMap {s : ℕ} (B : RowBasis s) : Vec s →ₗ[ℚ] Vec s :=
  LinearMap.id - ∑ i : Fin B.count,
    ((1 / dot (B.rows i) (B.rows i)) • dotRight (B.rows i)).smulRight (B.rows i)

theorem residualLinearMap_apply {s : ℕ} (B : RowBasis s) (v : Vec s) :
    residualLinearMap B v = residual B v := by
  simp [residualLinearMap, GodMoveRationalRowBasis.residual, projected, component,
    div_eq_mul_inv, mul_comm]

/-- Each row is computed by evaluating the residual on coordinate vectors. -/
def residualCoefficients {s : ℕ} (B : RowBasis s) (j i : Fin s) : ℚ :=
  residual B (Pi.single i (1 : ℚ)) j

theorem vector_eq_sum_coordinates {s : ℕ} (v : Vec s) :
    v = ∑ i : Fin s, v i • (Pi.single i (1 : ℚ) : Vec s) := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem residualCoefficients_functional {s : ℕ} (B : RowBasis s)
    (j : Fin s) (v : Vec s) :
    coefficientFunctional (residualCoefficients B j) v = residual B v j := by
  have he : residualLinearMap B v =
      ∑ i : Fin s, v i • residualLinearMap B (Pi.single i (1 : ℚ)) := by
    conv_lhs => rw [vector_eq_sum_coordinates v]
    simp only [map_sum, map_smul]
  have hj := congrFun he j
  simp only [residualLinearMap_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hj
  rw [coefficientFunctional_apply]
  simpa only [residualCoefficients, mul_comm] using hj.symm

theorem residual_ne_zero_iff_relation {s : ℕ} (B : RowBasis s) (v : Vec s) :
    residual B v ≠ 0 ↔
      ∃ j : Fin s, coefficientFunctional (residualCoefficients B j) v ≠ 0 := by
  classical
  simp only [residualCoefficients_functional]
  constructor
  · intro hne
    by_contra hn
    push_neg at hn
    apply hne
    funext j
    exact hn j
  · rintro ⟨j, hj⟩ he
    exact hj (congrFun he j)

theorem rationalValue_eq_residual_coordinate {s : ℕ} (B : RowBasis s)
    (j : Fin s) (bits : Fin s → Bool) :
    rationalValue (residualCoefficients B j) bits =
      residual B (fun i => bit (bits i)) j := by
  rw [rationalValue_eq_functional, residualCoefficients_functional]

/-- This is the original Boolean residual test on the actual circuit wires. -/
theorem accepts_iff_exists_relation {n : ℕ} (c : List (CGate n))
    (B : RowBasis c.length) (a : Assignment n) :
    accepts B (wireRow c a) = true ↔
      ∃ j : Fin c.length, rationalValue (residualCoefficients B j)
        (fun i => (runFrom a [] c).getD i.val false) ≠ 0 := by
  simp only [accepts, decide_eq_true_eq, residual_ne_zero_iff_relation]
  apply exists_congr
  intro j
  rw [rationalValue_eq_functional]
  rfl

/-- The maximum actual numerator/denominator bit length, computed from `q`. -/
def coefficientBits {s : ℕ} (q : Fin s → ℚ) : ℕ :=
  Finset.univ.sup (fun i => max (q i).num.natAbs.size (q i).den.size)

theorem coefficientBits_precision {s : ℕ} (q : Fin s → ℚ) :
    CoeffPrecision q (coefficientBits q) := by
  intro i
  have hmax : max (q i).num.natAbs.size (q i).den.size ≤ coefficientBits q :=
    Finset.le_sup (f := fun j : Fin s => max (q j).num.natAbs.size (q j).den.size)
      (Finset.mem_univ i)
  have hnum := (le_max_left (q i).num.natAbs.size (q i).den.size).trans hmax
  have hden := (le_max_right (q i).num.natAbs.size (q i).den.size).trans hmax
  exact ⟨(Nat.size_le.mp hnum).le, (Nat.size_le.mp hden).le⟩

/-- Every generated residual row comes with a computable precision budget. -/
theorem residualCoefficients_precision {s : ℕ} (B : RowBasis s) (j : Fin s) :
    CoeffPrecision (residualCoefficients B j)
      (coefficientBits (residualCoefficients B j)) :=
  coefficientBits_precision _

end GodMoveResidualQueries

#print axioms GodMoveResidualQueries.residualLinearMap_apply
#print axioms GodMoveResidualQueries.residualCoefficients_functional
#print axioms GodMoveResidualQueries.residual_ne_zero_iff_relation
#print axioms GodMoveResidualQueries.rationalValue_eq_residual_coordinate
#print axioms GodMoveResidualQueries.accepts_iff_exists_relation
#print axioms GodMoveResidualQueries.coefficientBits_precision
#print axioms GodMoveResidualQueries.residualCoefficients_precision
