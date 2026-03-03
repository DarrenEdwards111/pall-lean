/-
  CoeffLin.lean — MvPolynomial.coeff as a linear functional
-/
import Mathlib

namespace SpdpPaper

variable {σ F : Type*} [DecidableEq σ] [CommRing F]

/-- Coefficient extraction as a linear map. This is the "dual functional"
    used in Theorem 9.3 to establish the identity minor. -/
def coeffLin (m : σ →₀ ℕ) : MvPolynomial σ F →ₗ[F] F where
  toFun := fun p => MvPolynomial.coeff m p
  map_add' := fun p q => by simp [MvPolynomial.coeff_add]
  map_smul' := fun a p => by simp [MvPolynomial.coeff_smul]

/-- Kronecker delta for coeffLin on monomials -/
theorem coeffLin_monomial (m m' : σ →₀ ℕ) (a : F) :
    coeffLin m (MvPolynomial.monomial m' a : MvPolynomial σ F) =
    if m = m' then a else 0 := by
  simp [coeffLin, MvPolynomial.coeff_monomial, eq_comm]

end SpdpPaper
