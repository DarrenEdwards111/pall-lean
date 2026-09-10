import GodMoveQuadraticSheetLift

/-!
# Explicit affine-complement form of designated derivative rows

After multilinear projection and coordinate complementation, a selected
derivative row of the actual quadratic product is a complementary monomial
times a product of active affine factors. This identity uses no basis choice
and no unproved rank monotonicity for affine substitutions.
-/

namespace GodMoveDesignatedComplementRows

open MvPolynomial MultilinearSPDP SymmetricPower GodMoveQuadraticSheetLift
open scoped BigOperators

theorem mlProj_pderiv_boolFactor {m : ℕ} (i : Fin m) :
    mlProj (pderiv i (boolFactor m i)) = pderiv i (boolFactor m i) := by
  have hc : mlProj (C (-1) : Poly m) = C (-1) := by
    change mlProj (monomial 0 (-1 : ℚ)) = monomial 0 (-1 : ℚ)
    rw [mlProj_monomial]
    simp [Finsupp.IsMultilinear]
  have hn : mlProj (-1 : Poly m) = -1 := by simpa using hc
  rw [pderiv_boolFactor_self, mlProj_add, hn,
    show (2 : Poly m) = C 2 by simp [map_ofNat], C_mul', mlProj_smul, mlProj_X]

theorem mlProj_pderiv_boolFactor_prod {m : ℕ} (S : Finset (Fin m)) :
    mlProj (∏ i ∈ S, pderiv i (boolFactor m i)) =
      ∏ i ∈ S, pderiv i (boolFactor m i) := by
  classical
  rw [WithinProfileBound.mlProj_finset_prod_of_pairwise_disjoint_vars]
  · exact Finset.prod_congr rfl (fun i _ => mlProj_pderiv_boolFactor i)
  · intro i _ j _ hij
    exact Finset.disjoint_of_subset_left (derivativeFactor_vars_subset i)
      (Finset.disjoint_of_subset_right (derivativeFactor_vars_subset j) (by simp [hij]))

theorem affineComplement_pderiv_boolFactor {m : ℕ} (i : Fin m) :
    affineComplement m (pderiv i (boolFactor m i)) = (1 - 2 * X i : Poly m) := by
  rw [pderiv_boolFactor_self]
  simp only [map_add, map_neg, map_one, map_mul, map_ofNat, affineComplement_X]
  ring

/-- Explicit designated projected rows, with their untouched complementary
monomial and their active affine factors separated. -/
theorem complemented_qRow_factorization {m : ℕ} (S : Finset (Fin m)) :
    affineComplement m (mlProj (boolFactorDerivProd S)) =
      (∏ i ∈ S, (1 - 2 * X i : Poly m)) * GodMoveMonomialMinor.derivativeRow S := by
  have h := complemented_projected_row_factorization S (1 : Poly m) (by simp)
  simp only [one_mul, mlProj_pderiv_boolFactor_prod, map_prod,
    affineComplement_pderiv_boolFactor] at h
  exact h

end GodMoveDesignatedComplementRows

#print axioms GodMoveDesignatedComplementRows.mlProj_pderiv_boolFactor_prod
#print axioms GodMoveDesignatedComplementRows.complemented_qRow_factorization
