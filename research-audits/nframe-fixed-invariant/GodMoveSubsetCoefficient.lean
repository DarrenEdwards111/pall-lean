import GodMoveProjectorKernel
import GodMoveOperatorSubsetDAG

/-!
# Generic subset-coefficient identity for the shared recurrence

This is the ordinary commutative-ring algebra behind the exact kernel and
separated-input applications. The subset sum specifies the result; the shared
recurrence computes its coefficient without enumerating subsets.
-/

namespace GodMoveSubsetCoefficient

open GodMoveMonomialMinor GodMoveProjectorKernel
open scoped BigOperators

variable {R : Type*} [CommSemiring R] {m : ℕ}

theorem product_eq_subset_monomial_sum (A B : Fin m → R) :
    (∏ i, (Polynomial.C (A i) + Polynomial.C (B i) * Polynomial.X)) =
      ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset,
        Polynomial.monomial S.card
          ((∏ i ∈ S, B i) * ∏ i ∈ Finset.univ \ S, A i) := by
  classical
  have hfactor (i : Fin m) :
      Polynomial.C (A i) + Polynomial.C (B i) * Polynomial.X =
        Polynomial.monomial 1 (B i) + Polynomial.monomial 0 (A i) := by
    simp [Polynomial.C_mul_X_eq_monomial, add_comm]
  simp only [hfactor]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro S _
  rw [prod_univariate_monomial, prod_univariate_monomial]
  simp only [Finset.sum_const, smul_eq_mul, mul_one, mul_zero,
    Polynomial.monomial_mul_monomial, add_zero]

theorem coefficient_product_eq_subset_sum (A B : Fin m → R) (k : ℕ) :
    (∏ i, (Polynomial.C (A i) + Polynomial.C (B i) * Polynomial.X)).coeff k =
      ∑ S : KSubset m k, (∏ i ∈ S.val, B i) * ∏ i ∈ Finset.univ \ S.val, A i := by
  classical
  rw [product_eq_subset_monomial_sum, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [← Finset.sum_filter, ← Finset.powersetCard_eq_filter]
  exact (Finset.sum_coe_sort _ _).symm

theorem evalDAG_eq_subset_sum (A B : Fin m → R) (k : ℕ) :
    GodMoveOperatorSubsetDAG.evalDAG A B k =
      ∑ S : KSubset m k, (∏ i ∈ S.val, B i) * ∏ i ∈ Finset.univ \ S.val, A i := by
  rw [GodMoveOperatorSubsetDAG.evalDAG_eq_coefficient]
  exact coefficient_product_eq_subset_sum A B k

end GodMoveSubsetCoefficient

#print axioms GodMoveSubsetCoefficient.product_eq_subset_monomial_sum
#print axioms GodMoveSubsetCoefficient.coefficient_product_eq_subset_sum
#print axioms GodMoveSubsetCoefficient.evalDAG_eq_subset_sum
