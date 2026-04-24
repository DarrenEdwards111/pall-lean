import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

open Matrix

namespace PallLean.Paper93.DeepMath.NFrame

/-- For a symmetric matrix, transpose equals self. -/
theorem transpose_eq_of_isSymm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : A.IsSymm) :
    Aᵀ = A := h

/-- For a symmetric matrix, `(A + B).IsSymm` if both are symmetric. -/
theorem isSymm_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hB : B.IsSymm) :
    (A + B).IsSymm := by
  unfold Matrix.IsSymm at hA hB ⊢
  rw [Matrix.transpose_add, hA, hB]

/-- Symmetric matrix's i-th row equals i-th column (as functions). -/
theorem isSymm_row_eq_col {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : A.IsSymm) (i j : Fin n) :
    A i j = A j i := by
  have := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) h
  simp [Matrix.transpose_apply] at this
  exact this.symm

end PallLean.Paper93.DeepMath.NFrame
