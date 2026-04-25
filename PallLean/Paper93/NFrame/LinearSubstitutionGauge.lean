import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Rational matrix-induced linear substitutions

This file packages a rational matrix `A : Matrix (Fin N) (Fin N) ℚ` as the
`ℚ`-linear endomorphism of `MvPolynomial (Fin N) ℚ` induced by the variable
substitution

`X_i ↦ ∑ j, A i j • X_j`.

The construction is through the universal `MvPolynomial.aeval` algebra
homomorphism, with the gauge exposed as its underlying linear map.
-/

namespace PallLean
namespace Paper93
namespace NFrame

open MvPolynomial
open scoped BigOperators

variable {N : ℕ}

/-- The linear form in the polynomial variables determined by row `i` of `A`. -/
noncomputable def rationalMatrixLinearForm
    (A : Matrix (Fin N) (Fin N) ℚ) (i : Fin N) :
    MvPolynomial (Fin N) ℚ :=
  ∑ j : Fin N, A i j • (X j : MvPolynomial (Fin N) ℚ)

/-- The algebra homomorphism induced by the row-wise linear substitution
`X_i ↦ ∑ j, A i j • X_j`. -/
noncomputable def rationalMatrixSubstAlgHom
    (A : Matrix (Fin N) (Fin N) ℚ) :
    MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ :=
  aeval (rationalMatrixLinearForm A)

/-- The rational matrix-induced substitution gauge as a `ℚ`-linear map. -/
noncomputable def rationalMatrixSubstGauge
    (A : Matrix (Fin N) (Fin N) ℚ) :
    MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ :=
  (rationalMatrixSubstAlgHom A).toLinearMap

@[simp]
theorem rationalMatrixSubstGauge_X
    (A : Matrix (Fin N) (Fin N) ℚ) (i : Fin N) :
    rationalMatrixSubstGauge A (X i) = rationalMatrixLinearForm A i := by
  unfold rationalMatrixSubstGauge rationalMatrixSubstAlgHom
  rw [AlgHom.toLinearMap_apply, aeval_X]

@[simp]
theorem rationalMatrixSubstGauge_C
    (A : Matrix (Fin N) (Fin N) ℚ) (c : ℚ) :
    rationalMatrixSubstGauge A (C c : MvPolynomial (Fin N) ℚ) = C c := by
  unfold rationalMatrixSubstGauge rationalMatrixSubstAlgHom
  rw [AlgHom.toLinearMap_apply, aeval_C]
  rfl

@[simp]
theorem rationalMatrixLinearForm_one (i : Fin N) :
    rationalMatrixLinearForm (1 : Matrix (Fin N) (Fin N) ℚ) i =
      (X i : MvPolynomial (Fin N) ℚ) := by
  classical
  unfold rationalMatrixLinearForm
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro hi
    simp at hi

@[simp]
theorem rationalMatrixLinearForm_zero (i : Fin N) :
    rationalMatrixLinearForm (0 : Matrix (Fin N) (Fin N) ℚ) i =
      (0 : MvPolynomial (Fin N) ℚ) := by
  simp [rationalMatrixLinearForm]

@[simp]
theorem rationalMatrixSubstAlgHom_one :
    rationalMatrixSubstAlgHom (1 : Matrix (Fin N) (Fin N) ℚ) =
      AlgHom.id ℚ (MvPolynomial (Fin N) ℚ) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [rationalMatrixSubstAlgHom]

/-- The identity matrix induces the identity linear map on the polynomial ring. -/
@[simp]
theorem rationalMatrixSubstGauge_one :
    rationalMatrixSubstGauge (1 : Matrix (Fin N) (Fin N) ℚ) =
      LinearMap.id := by
  unfold rationalMatrixSubstGauge
  rw [rationalMatrixSubstAlgHom_one]
  rfl

/-- The zero matrix sends every variable to zero under the induced gauge. -/
@[simp]
theorem rationalMatrixSubstGauge_zero_X (i : Fin N) :
    rationalMatrixSubstGauge (0 : Matrix (Fin N) (Fin N) ℚ) (X i) =
      (0 : MvPolynomial (Fin N) ℚ) := by
  rw [rationalMatrixSubstGauge_X, rationalMatrixLinearForm_zero]

end NFrame
end Paper93
end PallLean
