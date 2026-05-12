/-
  PallLean/Paper93/Paper283/PrincipalMinorInverse.lean

  Paper §28.3 — Inverse of the PSD principal minor `A[J,J]`, used on
  the right-hand side of the δA Euler–Lagrange condition.

  * `principalMinor_invertible` : when the determinant of the principal
    minor is strictly positive, that determinant is a unit in `ℝ`
    (hence the minor itself is invertible as a matrix).
  * `sumPrincipalMinorInverses` : stub for the sum
    `Σ_J (A[J,J])^{-1}` as a full ambient `N × N` matrix. Extending
    each minor's inverse back to the ambient requires a zero-padding
    construction, deferred to a later file.
  * `sumPrincipalMinorInverses_at_identity` : sanity check that the
    stub reduces to `0` at `A = 1`.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import PallLean.Paper93.Paper283.PrincipalMinor

namespace PallLean.Paper93.Paper283

open Matrix

/-- For a PSD matrix `A` whose principal minor `A[J,J]` has strictly
    positive determinant, that determinant is a unit in `ℝ`. -/
theorem principalMinor_invertible {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (J : Finset (Fin N))
    (h : 0 < (principalMinor A J).det) :
    IsUnit (principalMinor A J).det :=
  (ne_of_gt h).isUnit

/-- Sum of principal minor inverses (RHS of δA Euler–Lagrange).
    Stub: the honest formula `Σ_J (A[J,J])^{-1}` requires extending
    each minor's inverse back to the ambient `N × N` matrix via
    zero-padding, which we defer. -/
noncomputable def sumPrincipalMinorInverses {N : ℕ}
    (_A : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  0

/-- At `A = 1` the stub evaluates to `0` by definition. -/
theorem sumPrincipalMinorInverses_at_identity (N : ℕ) :
    sumPrincipalMinorInverses (1 : Matrix (Fin N) (Fin N) ℝ) = 0 := rfl

end PallLean.Paper93.Paper283
