import GodMoveGaugeLocalOperators
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# A factored generating kernel for the actual production row projector

The coefficient of z^k in a product of m constant-size factors is exactly
the coefficient kernel of the existing rowProjection. Contracting that kernel
with the input's complemented coefficients recovers the actual projection.
This separates compact kernel construction from its potentially expensive
application to an implicitly represented input polynomial.
-/

namespace GodMoveProjectorKernel

open GodMoveMonomialMinor GodMoveDesignatedPositiveBoundary
open GodMoveBoundaryNFrameGauge GodMoveQuadraticSheetLift GodMoveGaugeLocalOperators
open scoped BigOperators

abbrev Poly (m : ℕ) := MvPolynomial (Fin m) ℚ
/-- The outer variables are dual coordinates; coefficients are output polynomials. -/
abbrev Kernel (m : ℕ) := MvPolynomial (Fin m) (Poly m)

noncomputable def branchA {m : ℕ} (i : Fin m) : Kernel m :=
  MvPolynomial.C (1 - MvPolynomial.X i) * MvPolynomial.X i

noncomputable def branchB {m : ℕ} (i : Fin m) : Kernel m :=
  MvPolynomial.C (2 * MvPolynomial.X i - 1)

/-- The defining coefficient kernel, written explicitly only for its semantics. -/
noncomputable def rowKernel (m k : ℕ) : Kernel m :=
  ∑ S : KSubset m k, MvPolynomial.monomial (complementaryColumn S.val) (qRow S.val)

/-- A product of m small factors generates all the row kernels. -/
noncomputable def generatingKernel (m : ℕ) : Polynomial (Kernel m) :=
  ∏ i : Fin m, (Polynomial.C (branchA i) + Polynomial.C (branchB i) * Polynomial.X)

theorem prod_outer_X {m : ℕ} (S : Finset (Fin m)) :
    (∏ i ∈ S, (MvPolynomial.X i : Kernel m)) =
      MvPolynomial.monomial (SymmetricPower.tagMonomial S) 1 := by
  rw [SymmetricPower.tagMonomial, MvPolynomial.monomial_sum_one]
  simp [MvPolynomial.X]

/-- Each binary branch choice has exactly the designated row as coefficient. -/
theorem branch_product {m : ℕ} (S : Finset (Fin m)) :
    (∏ i ∈ S, branchB i) * (∏ i ∈ Finset.univ \ S, branchA i) =
      MvPolynomial.monomial (complementaryColumn S) (qRow S) := by
  classical
  simp only [branchA, branchB, Finset.prod_mul_distrib, ← map_prod]
  rw [prod_outer_X, ← mul_assoc, ← map_mul, MvPolynomial.C_mul_monomial, mul_one]
  exact congrArg (MvPolynomial.monomial (complementaryColumn S)) (qRow_factorization S).symm

theorem prod_univariate_monomial {R : Type*} [CommSemiring R]
    {ι : Type*} (S : Finset ι) (d : ι → ℕ) (a : ι → R) :
    (∏ i ∈ S, Polynomial.monomial (d i) (a i)) =
      Polynomial.monomial (∑ i ∈ S, d i) (∏ i ∈ S, a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [hi, ih, Polynomial.monomial_mul_monomial]

/-- Expand the generating product by subset choices, preserving their sizes. -/
theorem generatingKernel_eq_sum (m : ℕ) :
    generatingKernel m =
      ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset,
        Polynomial.monomial S.card
          (MvPolynomial.monomial (complementaryColumn S) (qRow S)) := by
  classical
  unfold generatingKernel
  have hfactor (i : Fin m) :
      Polynomial.C (branchA i) + Polynomial.C (branchB i) * Polynomial.X =
        Polynomial.monomial 1 (branchB i) + Polynomial.monomial 0 (branchA i) := by
    simp [Polynomial.C_mul_X_eq_monomial, add_comm]
  simp only [hfactor]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro S _
  rw [prod_univariate_monomial, prod_univariate_monomial]
  simp only [Finset.sum_const, smul_eq_mul, mul_one, mul_zero,
    Polynomial.monomial_mul_monomial, add_zero]
  rw [branch_product]

/-- The selected coefficient is the actual binomial row kernel. -/
theorem generatingKernel_coeff (m k : ℕ) :
    (generatingKernel m).coeff k = rowKernel m k := by
  classical
  rw [generatingKernel_eq_sum, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [← Finset.sum_filter]
  rw [← Finset.powersetCard_eq_filter]
  exact (Finset.sum_coe_sort _ _).symm

/-- Pair the kernel's dual coordinates with the actual complemented input
coefficients. This contraction is not assigned a constant evaluation cost. -/
noncomputable def contract {m : ℕ} (p : Poly m) : Kernel m →ₗ[Poly m] Poly m :=
  Finsupp.linearCombination (Poly m)
    (fun d => MvPolynomial.C (MvPolynomial.coeff d (affineComplement m p)))

theorem contract_monomial {m : ℕ} (p : Poly m) (d : Fin m →₀ ℕ) (r : Poly m) :
    contract p (MvPolynomial.monomial d r) =
      MvPolynomial.coeff d (affineComplement m p) • r := by
  change Finsupp.linearCombination (Poly m)
    (fun e => MvPolynomial.C (MvPolynomial.coeff e (affineComplement m p)))
    (Finsupp.single d r) = _
  rw [Finsupp.linearCombination_single]
  simp [Algebra.smul_def, mul_comm]

/-- The kernel denotes exactly the existing production projection, on all
polynomials. No rank-preservation or coefficient advice is assumed. -/
theorem contract_rowKernel (m k : ℕ) (p : Poly m) :
    contract p (rowKernel m k) = rowProjection m k p := by
  simp only [rowKernel, map_sum, contract_monomial]
  rfl

theorem contract_generatingKernel_coeff (m k : ℕ) (p : Poly m) :
    contract p ((generatingKernel m).coeff k) = (boundaryGauge m k).projection p := by
  rw [generatingKernel_coeff, contract_rowKernel]
  rfl

end GodMoveProjectorKernel

#print axioms GodMoveProjectorKernel.branch_product
#print axioms GodMoveProjectorKernel.generatingKernel_eq_sum
#print axioms GodMoveProjectorKernel.generatingKernel_coeff
#print axioms GodMoveProjectorKernel.contract_monomial
#print axioms GodMoveProjectorKernel.contract_rowKernel
#print axioms GodMoveProjectorKernel.contract_generatingKernel_coeff
