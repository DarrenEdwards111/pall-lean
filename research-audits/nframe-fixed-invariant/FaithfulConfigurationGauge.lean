import PallLean.Paper93.DeepMath.NFrame.SNF
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

namespace FaithfulConfigurationGauge
open PallLean.Paper93.DeepMath.NFrame

def shear (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, c; 0, 1]
def gauge (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := (shear c).transpose * shear c

theorem shear_det (c : ℝ) : (shear c).det = 1 := by simp [shear, Matrix.det_fin_two]

theorem gauge_det (c : ℝ) : (gauge c).det = 1 := by
  simp [gauge, Matrix.det_mul, Matrix.det_transpose, shear_det]

theorem gauge_posDef (c : ℝ) : (gauge c).PosDef := by
  have hu : IsUnit (shear c) := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [shear_det]; exact isUnit_one)
  have h := (Matrix.IsUnit.posDef_star_left_conjugate_iff hu).mpr
    (Matrix.PosDef.one : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef)
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, gauge] using h

theorem gauge_entry (c : ℝ) : gauge c 0 1 = c := by
  simp [gauge, shear, Matrix.mul_apply, Fin.sum_univ_two]

theorem gauge_injective : Function.Injective gauge := by
  intro c d h
  have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) h
  simpa only [gauge_entry] using he

/-- Every real-coded state is retained, but the full fixed-field action is constant. -/
theorem action_constant (α β lam : ℝ)
    (adj : Matrix (Fin 2) (Fin 2) ℝ) (phi chi : Fin 2 → ℝ) (c d : ℝ) :
    S_NF α β lam adj phi chi (gauge c) = S_NF α β lam adj phi chi (gauge d) := by
  simp [S_NF, barrier, gauge_det]

/-- Applies to any transition and state coding; does not claim this is the intended holographic map. -/
theorem transition_zero_drop {State : Type*} (step : State → State) (code : State → ℝ)
    (s : State) (α β lam : ℝ) (adj : Matrix (Fin 2) (Fin 2) ℝ) (phi chi : Fin 2 → ℝ) :
    S_NF α β lam adj phi chi (gauge (code s)) -
      S_NF α β lam adj phi chi (gauge (code (step s))) = 0 := by
  rw [action_constant α β lam adj phi chi (code s) (code (step s)), sub_self]

theorem coded_gauge_injective {State : Type*} (code : State → ℝ)
    (hcode : Function.Injective code) : Function.Injective (gauge ∘ code) :=
  gauge_injective.comp hcode

end FaithfulConfigurationGauge
#print axioms FaithfulConfigurationGauge.gauge_posDef
#print axioms FaithfulConfigurationGauge.coded_gauge_injective
#print axioms FaithfulConfigurationGauge.transition_zero_drop
