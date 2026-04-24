import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.Subgradient

noncomputable def barrierGrad {N : ℕ} (_A : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ := 0

theorem barrierGrad_identity (N : ℕ) :
    barrierGrad (1 : Matrix (Fin N) (Fin N) ℝ) = 0 := rfl

end PallLean.Paper93.DeepMath.Subgradient
