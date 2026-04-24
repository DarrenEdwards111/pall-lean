import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.GraphSpectral

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [Semiring R]

/-- The row-sum function of a square matrix `A`: `rowSum A i = ∑ j, A i j`. -/
def rowSum (A : Matrix n n R) : n → R :=
  fun i => ∑ j, A i j

/-- The graph Laplacian of a square matrix `A`, defined as
`diagonal (rowSum A) - A`. -/
def laplacian {R : Type*} [Ring R] (A : Matrix n n R) : Matrix n n R :=
  Matrix.diagonal (rowSum A) - A

/-- The Laplacian of a symmetric real matrix (indexed by `Fin n`) is symmetric.
    This is the specialised, paper-faithful form: `L = D − A` with `D` a
    diagonal matrix. Since the diagonal is always symmetric and `A` is assumed
    symmetric, the difference `D − A` is symmetric. -/
theorem laplacian_isSymm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    (laplacian A).IsSymm :=
  (Matrix.isSymm_diagonal (rowSum A)).sub hA

end PallLean.Paper93.DeepMath.GraphSpectral
