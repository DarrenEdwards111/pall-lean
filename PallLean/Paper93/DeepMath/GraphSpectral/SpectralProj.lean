import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.GraphSpectral

noncomputable def spectralProj {N : ℕ}
    (_A : Matrix (Fin N) (Fin N) ℝ) (r : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => if i.val < r then (1:ℝ) else 0)

theorem spectralProj_zero {N} (A : Matrix (Fin N) (Fin N) ℝ) :
    spectralProj A 0 = 0 := by
  funext i j
  unfold spectralProj
  simp [Matrix.diagonal]
  all_goals (try split_ifs <;> omega)

end PallLean.Paper93.DeepMath.GraphSpectral
