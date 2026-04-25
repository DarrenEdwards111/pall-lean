import PallLean.Paper93.DeepMath.PathB.Positroid.PluckerAbstract
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- Principal minor of identity at any J equals 1. -/
theorem principalMinor_one_constant {n : ℕ} (J : Finset (Fin n)) :
    principalMinor (1 : Matrix (Fin n) (Fin n) ℝ) J = 1 :=
  principalMinor_one J

/-- Principal minor at empty set equals 1 universally. -/
theorem principalMinor_empty_universal {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    principalMinor M ∅ = 1 :=
  principalMinor_empty M

/-- Principal minor of identity at empty equals 1. -/
theorem principalMinor_one_empty {n : ℕ} :
    principalMinor (1 : Matrix (Fin n) (Fin n) ℝ) ∅ = 1 :=
  principalMinor_one ∅

/-- Principal minor of identity at any J in the satFamily equals 1. -/
theorem principalMinor_one_satFamily_member {n : ℕ} (J : Finset (Fin n)) :
    principalMinor (1 : Matrix (Fin n) (Fin n) ℝ) J = 1 :=
  principalMinor_one J

end PallLean.Paper93.DeepMath.PathB.Positroid
