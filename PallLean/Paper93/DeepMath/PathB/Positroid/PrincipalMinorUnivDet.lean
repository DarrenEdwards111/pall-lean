import PallLean.Paper93.DeepMath.PathB.Positroid.PluckerAbstract
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Principal minor at `Finset.univ` equals the determinant

This kernel-only file establishes the identity

    `principalMinor A Finset.univ = A.det`

for any square real matrix `A : Matrix (Fin n) (Fin n) ℝ`.

The proof unfolds the definition of `principalMinor`, exhibits the
canonical equivalence `(Finset.univ : Finset (Fin n)) ≃ Fin n` provided
by `Equiv.subtypeUnivEquiv`, rewrites the principal submatrix as a
`submatrix` along this equivalence, and then applies
`Matrix.det_submatrix_equiv_self`.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The principal minor at `Finset.univ` equals the determinant of the matrix.

This is the canonical Route C ⇒ Route A specialization: the determinant
recovers the principal minor at the full universe of indices. -/
theorem principalMinor_univ_det (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    principalMinor A (Finset.univ : Finset (Fin n)) = A.det := by
  unfold principalMinor
  let e : (Finset.univ : Finset (Fin n)) ≃ Fin n :=
    Equiv.subtypeUnivEquiv (fun i : Fin n => Finset.mem_univ i)
  have hsub :
      A.submatrix (fun i : (Finset.univ : Finset (Fin n)) => (i.val : Fin n))
                  (fun j : (Finset.univ : Finset (Fin n)) => (j.val : Fin n))
        = A.submatrix e e := rfl
  rw [hsub]
  exact Matrix.det_submatrix_equiv_self e A

/-- Symmetric form: the determinant equals the principal minor at `Finset.univ`. -/
theorem det_eq_principalMinor_univ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    A.det = principalMinor A (Finset.univ : Finset (Fin n)) :=
  (principalMinor_univ_det n A).symm

end PallLean.Paper93.DeepMath.PathB.Positroid
