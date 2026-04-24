/-
  PallLean/Paper93/Paper283/PrincipalMinor.lean

  Paper §28.3 — Principal minor `A[J,J]` for a matrix `A` and an
  index set `J ⊆ Fin N`. This file defines the principal minor
  operation and proves two basic sanity lemmas:

    * `principalMinor_one` : principal minor of the identity is the
      identity on the restricted index set;
    * `principalMinor_one_det` : its determinant equals `1`.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

namespace PallLean.Paper93.Paper283

open Matrix

/-- Principal minor `A[J,J]`: restrict `A` to rows/columns in `J`. -/
noncomputable def principalMinor {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (J : Finset (Fin N)) :
    Matrix J J ℝ :=
  fun i j => A i.val j.val

/-- Principal minor of identity is identity. -/
theorem principalMinor_one {N : ℕ} {J : Finset (Fin N)} :
    principalMinor (1 : Matrix (Fin N) (Fin N) ℝ) J = 1 := by
  funext i j
  unfold principalMinor
  by_cases h : i = j
  · rw [h]; simp [Matrix.one_apply]
  · simp [Matrix.one_apply, h, Subtype.ext_iff]

/-- Det of principal minor of identity = 1. -/
theorem principalMinor_one_det {N : ℕ} {J : Finset (Fin N)} :
    (principalMinor (1 : Matrix (Fin N) (Fin N) ℝ) J).det = 1 := by
  rw [principalMinor_one, Matrix.det_one]

end PallLean.Paper93.Paper283
