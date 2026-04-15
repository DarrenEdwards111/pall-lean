import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Rank

namespace CoeffMatrixHelpers

open MvPolynomial Matrix

variable {σ : Type*} [DecidableEq σ]
variable {F : Type*} [Field F]

/-- Coefficient matrix of a finite family of polynomials restricted to a finite monomial set. -/
noncomputable def coeffMatrix {ι : Type*}
    (monomials : Finset (σ →₀ ℕ)) (generators : ι → MvPolynomial σ F) :
    Matrix ι monomials F :=
  fun i m => MvPolynomial.coeff m.1 (generators i)

/-- Column-action matrix induced by a linear map on monomial basis vectors. -/
noncomputable def monomialActionMatrix
    (src tgt : Finset (σ →₀ ℕ)) (φ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F) :
    Matrix src tgt F :=
  fun s t => MvPolynomial.coeff t.1 (φ (MvPolynomial.monomial s.1 (1 : F)))

theorem coeff_apply_eq_sum_monomialActionMatrix
    (src : Finset (σ →₀ ℕ))
    (φ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (p : MvPolynomial σ F)
    (hp : p.support ⊆ src)
    (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (φ p) =
      ∑ d : src, MvPolynomial.coeff d.1 p *
        MvPolynomial.coeff m (φ (MvPolynomial.monomial d.1 (1 : F))) := by
  calc
    MvPolynomial.coeff m (φ p)
        = MvPolynomial.coeff m
            (φ (p.support.sum fun d =>
              MvPolynomial.monomial d (MvPolynomial.coeff d p))) := by
              rw [← p.as_sum]
    _ = MvPolynomial.coeff m
          (p.support.sum fun d => φ (MvPolynomial.monomial d (MvPolynomial.coeff d p))) := by
            rw [map_sum]
    _ = MvPolynomial.coeff m
          (p.support.sum fun d => MvPolynomial.coeff d p •
            φ (MvPolynomial.monomial d (1 : F))) := by
            apply congrArg (MvPolynomial.coeff m)
            congr 1 with d
            rw [show MvPolynomial.monomial d (MvPolynomial.coeff d p) =
                MvPolynomial.coeff d p • MvPolynomial.monomial d (1 : F) by
                  rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
              map_smul]
    _ = p.support.sum (fun d => MvPolynomial.coeff d p *
          MvPolynomial.coeff m (φ (MvPolynomial.monomial d (1 : F)))) := by
            rw [MvPolynomial.coeff_sum]
            apply Finset.sum_congr rfl
            intro d hd
            rw [MvPolynomial.coeff_smul, smul_eq_mul]
    _ = src.sum (fun d => MvPolynomial.coeff d p *
          MvPolynomial.coeff m (φ (MvPolynomial.monomial d (1 : F)))) := by
            exact Finset.sum_subset hp (by
              intro d hdsrc hdnot
              rw [MvPolynomial.notMem_support_iff.mp hdnot, zero_mul])
    _ = ∑ d : src, MvPolynomial.coeff d.1 p *
          MvPolynomial.coeff m (φ (MvPolynomial.monomial d.1 (1 : F))) := by
            rw [← src.sum_attach (f := fun d =>
              MvPolynomial.coeff d p *
                MvPolynomial.coeff m (φ (MvPolynomial.monomial d (1 : F))))]
            rw [Finset.attach_eq_univ]

theorem coeffMatrix_map_eq_mul_monomialActionMatrix {ι : Type*} [Fintype ι]
    (src tgt : Finset (σ →₀ ℕ))
    (φ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (generators : ι → MvPolynomial σ F)
    (hsupport : ∀ i, (generators i).support ⊆ src) :
    coeffMatrix tgt (fun i => φ (generators i)) =
      coeffMatrix src generators * monomialActionMatrix src tgt φ := by
  ext i t
  simpa [coeffMatrix, monomialActionMatrix, Matrix.mul_apply] using
    coeff_apply_eq_sum_monomialActionMatrix src φ (generators i) (hsupport i) t.1

theorem rank_coeffMatrix_map_le {ι : Type*} [Fintype ι]
    (src tgt : Finset (σ →₀ ℕ))
    (φ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (generators : ι → MvPolynomial σ F)
    (hsupport : ∀ i, (generators i).support ⊆ src) :
    (coeffMatrix tgt (fun i => φ (generators i))).rank ≤
      (coeffMatrix src generators).rank := by
  rw [coeffMatrix_map_eq_mul_monomialActionMatrix src tgt φ generators hsupport]
  exact Matrix.rank_mul_le_left _ _

end CoeffMatrixHelpers
