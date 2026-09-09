import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic

namespace ShiftedLogDetOverlap

/-- One-dimensional positive local gadget, used to test overlapping contributions. -/
def localMatrix (a : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := Matrix.diagonal (fun _ => a)

noncomputable def shiftedLogDet (A : Matrix (Fin 1) (Fin 1) ℝ) : ℝ :=
  Real.log ((1 + A).det)

theorem local_posDef {a : ℝ} (ha : 0 < a) : (localMatrix a).PosDef :=
  Matrix.posDef_diagonal_iff.mpr (fun _ => ha)

theorem local_shifted_log (a : ℝ) : shiftedLogDet (localMatrix a) = Real.log (1+a) := by
  simp [shiftedLogDet, localMatrix]

theorem overlapping_shifted_log (a b : ℝ) :
    shiftedLogDet (localMatrix a + localMatrix b) = Real.log (1+a+b) := by
  simp [shiftedLogDet, localMatrix, add_assoc]

/-- Local log-det contributions cannot be summed as a global lower bound on overlapping directions. -/
theorem overlap_strictly_less_than_sum {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    shiftedLogDet (localMatrix a + localMatrix b) <
      shiftedLogDet (localMatrix a) + shiftedLogDet (localMatrix b) := by
  rw [overlapping_shifted_log, local_shifted_log, local_shifted_log,
    ← Real.log_mul (by positivity : 1+a ≠ 0) (by positivity : 1+b ≠ 0)]
  apply Real.log_lt_log (by positivity)
  nlinarith [mul_pos ha hb]

/-- The genuine added contribution is a ratio relative to the already accumulated matrix. -/
theorem exact_marginal {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    shiftedLogDet (localMatrix a + localMatrix b) - shiftedLogDet (localMatrix a) =
      Real.log (1 + b / (1+a)) := by
  rw [overlapping_shifted_log, local_shifted_log,
    ← Real.log_div (by positivity : 1+a+b ≠ 0) (by positivity : 1+a ≠ 0)]
  congr 1
  field_simp

/-- Exact condition for a proposed positive marginal lower bound in the overlap test. -/
theorem marginal_lower_iff {a b delta : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    delta ≤ shiftedLogDet (localMatrix a + localMatrix b) - shiftedLogDet (localMatrix a) ↔
      (Real.exp delta - 1) * (1+a) ≤ b := by
  rw [exact_marginal ha hb, Real.le_log_iff_exp_le (by positivity)]
  have hp : 0 < 1+a := by positivity
  calc
    Real.exp delta ≤ 1 + b / (1+a) ↔ Real.exp delta - 1 ≤ b / (1+a) := by constructor <;> intro h <;> linarith
    _ ↔ (Real.exp delta - 1) * (1+a) ≤ b := le_div_iff₀ hp

end ShiftedLogDetOverlap
#print axioms ShiftedLogDetOverlap.local_posDef
#print axioms ShiftedLogDetOverlap.overlap_strictly_less_than_sum
#print axioms ShiftedLogDetOverlap.exact_marginal

#print axioms ShiftedLogDetOverlap.marginal_lower_iff
