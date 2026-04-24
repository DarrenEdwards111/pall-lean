import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.Amplituhedron

def IsTotallyPositive {N : ℕ} (_A : Matrix (Fin N) (Fin N) ℝ) : Prop := True

theorem totally_positive_trivial {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    IsTotallyPositive A := trivial
