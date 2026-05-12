import PallLean.Paper93.DeepMath.PathB.Positroid.PluckerAbstract
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# `principalMinor A ∅ = 1` for arbitrary square real matrices

This kernel-only file packages the empty-subset evaluation of the
`principalMinor` map (defined in
`PallLean.Paper93.DeepMath.PathB.Positroid.PluckerAbstract`) for an
arbitrary square real matrix `A`.

The principal minor at the empty subset is the determinant of the `0 × 0`
submatrix indexed by the empty subtype `(∅ : Finset (Fin n))`.  Since the
indexing type is empty, the determinant of the resulting matrix is `1`
by Mathlib's convention `Matrix.det_isEmpty`.

In addition, we package the universe case
(`principalMinor A Finset.univ = A.det`) as
`principalMinor_univ_det`, providing a Route C ⇒ Route A bridge in which
the principal minor at the universe specializes to the full determinant.

The file is kernel-only: no `sorry`, no custom `axiom`; only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid
namespace PrincipalMinorEmptyOne

/-- The principal minor of any square real matrix at the empty subset is `1`.

This is the empty-subset specialization of `principalMinor_empty`: the
underlying `0 × 0` submatrix has empty index type, so its determinant
is `1` by `Matrix.det_isEmpty`. -/
theorem principalMinor_empty_one
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    principalMinor A (∅ : Finset (Fin n)) = 1 :=
  principalMinor_empty A

/-- The principal minor of any square real matrix at `Finset.univ` equals
the determinant of the matrix.

This is the universe-subset specialization of `principalMinor_univ`:
the principal submatrix indexed by `Finset.univ` is the original matrix
up to reindexing by an equivalence with `Fin n`, and the determinant is
preserved under such reindexing. -/
theorem principalMinor_univ_det
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    principalMinor A (Finset.univ : Finset (Fin n)) = A.det :=
  principalMinor_univ A

end PrincipalMinorEmptyOne
end PallLean.Paper93.DeepMath.PathB.Positroid
