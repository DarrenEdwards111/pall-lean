import PallLean.Paper93.DeepMath.PathB.Positroid.PluckerAbstract
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Principal minor at the empty subset equals 1

This kernel-only file packages corollaries of `principalMinor_empty`
specialized to:

* an arbitrary square real matrix,
* the identity matrix `1`, and
* the zero matrix `0`.

In all three cases the principal minor at the empty subset evaluates to
`1`, since it is the determinant of the empty matrix.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The principal minor of any square real matrix at the empty subset is `1`. -/
theorem principalMinor_empty_any (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    principalMinor M ∅ = 1 :=
  principalMinor_empty M

/-- The principal minor of the identity matrix at the empty subset is `1`. -/
theorem principalMinor_empty_one (n : ℕ) :
    principalMinor (1 : Matrix (Fin n) (Fin n) ℝ) ∅ = 1 :=
  principalMinor_empty 1

/-- The principal minor of the zero matrix at the empty subset is `1`. -/
theorem principalMinor_empty_zero (n : ℕ) :
    principalMinor (0 : Matrix (Fin n) (Fin n) ℝ) ∅ = 1 :=
  principalMinor_empty 0

end PallLean.Paper93.DeepMath.PathB.Positroid
