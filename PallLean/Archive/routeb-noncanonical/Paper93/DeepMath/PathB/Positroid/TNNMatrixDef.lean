import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Totally non-negative (principal-TNN) matrices

This file defines the notion of a **principal-TNN** square matrix: a matrix
all of whose principal minors (determinants of submatrices indexed by a
common subset `J` on both rows and columns) are non-negative.

We also define the strict version, **principal-TP**, requiring strict
positivity of every principal minor.

Principal-TNN is a weaker condition than full total non-negativity (which
demands non-negativity of *all* minors, not only principal ones), but is
the relevant condition for many positroid-stratification applications and
for the §7.1 amplituhedron gauge construction.

The identity matrix is shown to be principal-TP (and hence principal-TNN),
since every principal minor of the identity is `1`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- A square matrix is **principal-TNN** if every principal minor is non-negative. -/
def IsPrincipalTNN {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ (J : Finset (Fin n)),
    0 ≤ (A.submatrix (fun i : J => i.val) (fun j : J => j.val)).det

/-- A square matrix is **principal-TP** (totally positive) if every principal minor is strictly positive. -/
def IsPrincipalTP {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ (J : Finset (Fin n)),
    0 < (A.submatrix (fun i : J => i.val) (fun j : J => j.val)).det

/-- Principal-TP implies principal-TNN. -/
theorem IsPrincipalTP.toTNN {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (h : IsPrincipalTP A) : IsPrincipalTNN A := fun J => le_of_lt (h J)

/-- The identity matrix is principal-TNN: every principal minor of the identity
    is 1, which is positive (hence non-negative). -/
theorem identity_isPrincipalTNN (n : ℕ) :
    IsPrincipalTNN (1 : Matrix (Fin n) (Fin n) ℝ) := by
  intro J
  -- Use Matrix.submatrix_one with injectivity of Subtype.val
  have hInj : Function.Injective (fun i : J => (i.val : Fin n)) :=
    fun _ _ h => Subtype.ext h
  rw [Matrix.submatrix_one _ hInj, Matrix.det_one]
  norm_num

/-- The identity matrix is principal-TP: every principal minor of the identity is exactly 1, hence positive. -/
theorem identity_isPrincipalTP (n : ℕ) :
    IsPrincipalTP (1 : Matrix (Fin n) (Fin n) ℝ) := by
  intro J
  have hInj : Function.Injective (fun i : J => (i.val : Fin n)) :=
    fun _ _ h => Subtype.ext h
  rw [Matrix.submatrix_one _ hInj, Matrix.det_one]
  norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid
