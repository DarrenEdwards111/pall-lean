import PallLean.Paper93.DeepMath.PathB.Positroid.PluckerAbstract
import PallLean.Paper93.DeepMath.PathB.PrincipalMinorAtUniv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB

/-- The principal minor of the identity matrix at any J equals 1. -/
theorem principalMinor_of_identity_eq_one {n : ℕ} (J : Finset (Fin n)) :
    principalMinor (1 : Matrix (Fin n) (Fin n) ℝ) J = 1 :=
  principalMinor_one J

/-- Identity matrix has principal minor 1 at empty subset. -/
theorem identity_minor_at_empty (n : ℕ) :
    principalMinor (1 : Matrix (Fin n) (Fin n) ℝ) ∅ = 1 :=
  principalMinor_one ∅

/-- Identity matrix has principal minor 1 at universe. -/
theorem identity_minor_at_univ (n : ℕ) :
    principalMinor (1 : Matrix (Fin n) (Fin n) ℝ) Finset.univ = 1 :=
  principalMinor_one Finset.univ

/-- Identity matrix's determinant equals 1. -/
theorem identity_det_eq_one (n : ℕ) :
    (1 : Matrix (Fin n) (Fin n) ℝ).det = 1 := Matrix.det_one

/-- Identity matrix's principal minor at any J coincides with the determinant of identity. -/
theorem identity_minor_eq_det_self {n : ℕ} (J : Finset (Fin n)) :
    principalMinor (1 : Matrix (Fin n) (Fin n) ℝ) J = (1 : Matrix (Fin n) (Fin n) ℝ).det := by
  rw [principalMinor_one, Matrix.det_one]

end PallLean.Paper93.DeepMath.PathB.Positroid
