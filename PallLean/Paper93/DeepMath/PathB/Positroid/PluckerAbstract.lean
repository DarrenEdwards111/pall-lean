import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Plücker-coordinate-style abstraction (specialized to principal minors)

This file defines a kernel-only abstraction for a Plücker-style map
specialized to principal minors of square matrices, and proves basic
structural properties:

* `principalMinor_empty` — the principal minor at the empty subset is `1`;
* `principalMinor_one` — the principal minor of the identity matrix at any
  subset is `1`;
* `principalMinor_univ` — the principal minor at `Finset.univ` equals the
  determinant of the matrix;
* `principalMinor_one_univ` — the principal minor of the identity matrix at
  the universe is `1`.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The principal-minor map: sends `(A, J)` to the determinant of the principal
    submatrix of `A` at index set `J`. -/
def principalMinor {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (J : Finset (Fin n)) : ℝ :=
  (A.submatrix (fun i : J => (i.val : Fin n)) (fun j : J => (j.val : Fin n))).det

/-- The principal minor of any matrix at the empty subset is 1. -/
theorem principalMinor_empty {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    principalMinor A ∅ = 1 := by
  unfold principalMinor
  exact Matrix.det_isEmpty

/-- The principal minor of the identity matrix at any subset is 1. -/
theorem principalMinor_one {n : ℕ} (J : Finset (Fin n)) :
    principalMinor (1 : Matrix (Fin n) (Fin n) ℝ) J = 1 := by
  unfold principalMinor
  have hInj : Function.Injective (fun i : J => (i.val : Fin n)) :=
    fun _ _ h => Subtype.ext h
  rw [Matrix.submatrix_one _ hInj, Matrix.det_one]

/-- The principal minor at `Finset.univ` equals the determinant. -/
theorem principalMinor_univ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    principalMinor A Finset.univ = A.det := by
  unfold principalMinor
  let e : (Finset.univ : Finset (Fin n)) ≃ Fin n :=
    Equiv.subtypeUnivEquiv (fun i : Fin n => Finset.mem_univ i)
  have hsub :
      A.submatrix (fun i : (Finset.univ : Finset (Fin n)) => i.val)
                  (fun j : (Finset.univ : Finset (Fin n)) => j.val)
        = A.submatrix e e := rfl
  rw [hsub]
  exact Matrix.det_submatrix_equiv_self e A

/-- The principal minor of the identity matrix at the universe equals 1. -/
theorem principalMinor_one_univ {n : ℕ} :
    principalMinor (1 : Matrix (Fin n) (Fin n) ℝ) Finset.univ = 1 :=
  principalMinor_one Finset.univ

end PallLean.Paper93.DeepMath.PathB.Positroid
