import PallLean.Paper93.DeepMath.NFrame.SNF
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

namespace NFrameCongruenceStep
open PallLean.Paper93.DeepMath.NFrame

theorem congruence_posDef {n : ℕ} (A U : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hU : IsUnit U) : (U.transpose * A * U).PosDef := by
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    using (Matrix.IsUnit.posDef_star_left_conjugate_iff hU).mpr hA

theorem barrier_congruence_drop {n : ℕ} (A U : Matrix (Fin n) (Fin n) ℝ)
    (hA : 0 < A.det) (hU : 0 < U.det) :
    barrier A - barrier (U.transpose * A * U) = 2 * Real.log U.det := by
  unfold barrier
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Real.log_mul (mul_ne_zero (ne_of_gt hU) (ne_of_gt hA)) (ne_of_gt hU),
    Real.log_mul (ne_of_gt hU) (ne_of_gt hA)]
  ring

/-- Other fields are held fixed; not a universal machine simulation theorem. -/
theorem full_action_congruence_drop {n : ℕ} (α β lam : ℝ)
    (adj A U : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ)
    (hA : 0 < A.det) (hU : 0 < U.det) :
    S_NF α β lam adj phi chi A - S_NF α β lam adj phi chi (U.transpose * A * U)
      = lam * (2 * Real.log U.det) := by
  have h := barrier_congruence_drop A U hA hU
  unfold S_NF
  rw [← h]
  ring

/-- Determinant-one congruences cannot discharge the fixed-field action. -/
theorem full_action_det_one {n : ℕ} (α β lam : ℝ)
    (adj A U : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ)
    (hA : 0 < A.det) (hU : U.det = 1) :
    S_NF α β lam adj phi chi A = S_NF α β lam adj phi chi (U.transpose * A * U) := by
  have h := full_action_congruence_drop α β lam adj A U phi chi hA (by rw [hU]; norm_num)
  rw [hU, Real.log_one] at h
  linarith

end NFrameCongruenceStep
#print axioms NFrameCongruenceStep.congruence_posDef
#print axioms NFrameCongruenceStep.full_action_congruence_drop
#print axioms NFrameCongruenceStep.full_action_det_one
