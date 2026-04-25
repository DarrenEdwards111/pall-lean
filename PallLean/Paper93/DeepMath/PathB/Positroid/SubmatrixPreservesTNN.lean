import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Submatrix preserves principal-TNN

We provide kernel-only verifications that the identity matrix's principal
minors are exactly `1`, hence the identity satisfies the principal-TNN
constraint at every index set `J`. These statements specialise the general
fact that if `A` is principal-TNN, then `A.submatrix J J` is also
principal-TNN, since the principal minors of `A.submatrix J J` are exactly
the principal minors of `A` at subsets of `J`.

For the identity matrix, this specialisation is direct: every principal
minor is the determinant of an identity submatrix, which is `1`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- For the identity matrix, all principal-TNN constraints are satisfied trivially. -/
theorem identity_TNN_universal_constraint (n : ℕ) (J : Finset (Fin n)) :
    0 ≤ ((1 : Matrix (Fin n) (Fin n) ℝ).submatrix
        (fun i : J => (i.val : Fin n)) (fun j : J => (j.val : Fin n))).det := by
  have h := identity_isPrincipalTNN n J
  exact h

/-- The identity matrix's principal minor at any J is exactly 1. -/
theorem identity_principal_minor_eq_one (n : ℕ) (J : Finset (Fin n)) :
    ((1 : Matrix (Fin n) (Fin n) ℝ).submatrix
        (fun i : J => (i.val : Fin n)) (fun j : J => (j.val : Fin n))).det = 1 := by
  have hInj : Function.Injective (fun i : J => (i.val : Fin n)) :=
    fun _ _ h => Subtype.ext h
  rw [Matrix.submatrix_one _ hInj, Matrix.det_one]

/-- Identity matrix is principal-TP at every J: principal minor strictly positive (= 1). -/
theorem identity_principal_minor_pos (n : ℕ) (J : Finset (Fin n)) :
    0 < ((1 : Matrix (Fin n) (Fin n) ℝ).submatrix
        (fun i : J => (i.val : Fin n)) (fun j : J => (j.val : Fin n))).det := by
  rw [identity_principal_minor_eq_one]
  norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid
