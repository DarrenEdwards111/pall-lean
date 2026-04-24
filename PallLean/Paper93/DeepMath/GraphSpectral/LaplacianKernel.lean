import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.GraphSpectral

/-- The concrete 2×2 graph Laplacian of the single-edge graph on two vertices. -/
def L : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; -1, 1]

/-- The all-ones vector in `Fin 2 → ℝ`. -/
def u : Fin 2 → ℝ := ![1, 1]

/-- The all-ones vector lies in the kernel of the 2×2 graph Laplacian:
`L.mulVec u = 0`. -/
theorem laplacian_mulVec_ones_eq_zero : L.mulVec u = 0 := by
  funext i
  fin_cases i
  · show (L.mulVec u) 0 = (0 : ℝ)
    simp only [L, u, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    ring
  · show (L.mulVec u) 1 = (0 : ℝ)
    simp only [L, u, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    ring

end PallLean.Paper93.DeepMath.GraphSpectral
