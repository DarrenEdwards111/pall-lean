import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Principal minor at `Finset.univ`

This file proves that the principal minor of any square matrix at the full
index set `Finset.univ` equals the determinant of the matrix itself, and
specialises this to the identity matrix where every principal minor equals 1.

The proof of the first theorem reduces the principal-minor submatrix to a
relabelling of `M` along the equivalence
`Equiv.subtypeUnivEquiv : ↥(Finset.univ : Finset (Fin n)) ≃ Fin n`
and applies `Matrix.det_submatrix_equiv_self`.

The second theorem uses `Matrix.submatrix_one` together with the injectivity
of `Subtype.val`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Matrix

/-- The principal minor of any square matrix at the full index set
    `Finset.univ` equals the determinant of the matrix itself. -/
theorem principalMinor_at_univ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (M.submatrix (fun i : (Finset.univ : Finset (Fin n)) => i.val)
                 (fun j : (Finset.univ : Finset (Fin n)) => j.val)).det = M.det := by
  -- The map `i ↦ i.val` from `↥(univ : Finset (Fin n))` to `Fin n` is the
  -- forward direction of the canonical equivalence `Equiv.subtypeUnivEquiv`.
  let e : (Finset.univ : Finset (Fin n)) ≃ Fin n :=
    Equiv.subtypeUnivEquiv (fun i : Fin n => Finset.mem_univ i)
  -- The submatrix in question is exactly `M.submatrix e e`.
  have hsub :
      M.submatrix (fun i : (Finset.univ : Finset (Fin n)) => i.val)
                  (fun j : (Finset.univ : Finset (Fin n)) => j.val)
        = M.submatrix (fun i => e i) (fun j => e j) := rfl
  rw [hsub]
  -- Reindexing along an equivalence on both sides preserves the determinant.
  exact Matrix.det_submatrix_equiv_self e M

/-- The principal minor of the identity matrix at any subset is 1. -/
theorem principalMinor_one_eq_one {n : ℕ} (J : Finset (Fin n)) :
    ((1 : Matrix (Fin n) (Fin n) ℝ).submatrix
        (fun i : J => i.val) (fun j : J => j.val)).det = 1 := by
  -- The map `Subtype.val : ↥J → Fin n` is injective.
  have hInj : Function.Injective (fun i : J => (i.val : Fin n)) :=
    fun _ _ h => Subtype.ext h
  -- The principal submatrix of the identity along an injective map is the
  -- identity on the smaller index type.
  rw [Matrix.submatrix_one _ hInj, Matrix.det_one]

end PallLean.Paper93.DeepMath.PathB
