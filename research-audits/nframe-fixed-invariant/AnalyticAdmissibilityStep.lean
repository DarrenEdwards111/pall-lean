import PallLean.Paper93.DeepMath.NFrame.SNF
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

namespace NFrameAdmissibilityStep
open PallLean.Paper93.DeepMath.NFrame

noncomputable def scalarGauge (s : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  Matrix.diagonal (fun _ => Real.exp s)

theorem scalarGauge_posDef (s : ℝ) : (scalarGauge s).PosDef := by
  exact Matrix.posDef_diagonal_iff.mpr (fun _ => Real.exp_pos s)

theorem scalarGauge_barrier (s : ℝ) : barrier (scalarGauge s) = -s := by
  simp [barrier, Matrix.det_fin_one, scalarGauge]

/-- Exact change of the existing full action, with every other field fixed.
    This is NOT asserted to be a realizable machine transition. -/
theorem full_action_drop (α β lam s t : ℝ)
    (adj : Matrix (Fin 1) (Fin 1) ℝ) (phi chi : Fin 1 → ℝ) :
    S_NF α β lam adj phi chi (scalarGauge s) -
      S_NF α β lam adj phi chi (scalarGauge t) = lam * (t - s) := by
  unfold S_NF
  rw [scalarGauge_barrier, scalarGauge_barrier]
  ring

/-- Positive definiteness alone cannot bound an action drop, even in dimension one. -/
theorem admissibility_does_not_bound_drop (α β lam r : ℝ) (hlam : 0 < lam)
    (adj : Matrix (Fin 1) (Fin 1) ℝ) (phi chi : Fin 1 → ℝ) :
    ∃ A B : Matrix (Fin 1) (Fin 1) ℝ, A.PosDef ∧ B.PosDef ∧
      r < S_NF α β lam adj phi chi A - S_NF α β lam adj phi chi B := by
  refine ⟨scalarGauge 0, scalarGauge ((r + 1) / lam),
    scalarGauge_posDef _, scalarGauge_posDef _, ?_⟩
  rw [full_action_drop]
  have hn : lam ≠ 0 := ne_of_gt hlam
  field_simp
  nlinarith

end NFrameAdmissibilityStep
#print axioms NFrameAdmissibilityStep.full_action_drop
#print axioms NFrameAdmissibilityStep.admissibility_does_not_bound_drop
