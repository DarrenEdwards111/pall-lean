import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB

/-- For a diagonal matrix `Matrix.diagonal d` with `d i = 1` for all i in some set J,
    the principal minor at J equals 1. (Trivial: submatrix is identity.) -/
theorem diagonal_unit_at_J {n k : ℕ} (J : Fin k → Fin n) (hInj : Function.Injective J)
    (d : Fin n → ℝ) (h : ∀ i : Fin k, d (J i) = 1) :
    ((Matrix.diagonal d).submatrix J J).det = 1 := by
  -- The submatrix is itself diagonal with diagonal entries d (J i), all equal to 1.
  -- So the submatrix is the identity, det = 1.
  have h_eq : (Matrix.diagonal d).submatrix J J = Matrix.diagonal (fun i => d (J i)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.submatrix_apply, Matrix.diagonal_apply_eq]
    · have hJij : J i ≠ J j := fun heq => hij (hInj heq)
      simp [Matrix.submatrix_apply, Matrix.diagonal_apply_ne _ hJij,
            Matrix.diagonal_apply_ne _ hij]
  rw [h_eq, Matrix.det_diagonal]
  have h1 : ∀ i : Fin k, d (J i) = (1 : ℝ) := h
  simp [h1]

end PallLean.Paper93.DeepMath.PathB
