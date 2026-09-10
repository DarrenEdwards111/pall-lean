import GodMoveBoundaryNFrameGauge
import GodMoveMultilinearRestriction

/-!
# Local derivative/evaluation operators for the retained-row projection

Each coordinate contributes either A_i p = -(1-X_i)(∂_i p)|_(X_i=1)
or B_i p = (2X_i-1)p|_(X_i=1). These are actual rational polynomial linear
maps, not assumed low-rank labels. Operators on distinct coordinates commute.
Applying such an operator to a compact input circuit still requires derivative
and evaluation work; a short operator expression is not a runtime bound.
-/

namespace GodMoveGaugeLocalOperators

open MvPolynomial PiStarConcrete
open GodMoveMonomialMinor

abbrev Poly (m : ℕ) := MvPolynomial (Fin m) ℚ

noncomputable def evalAtOne {m : ℕ} (i : Fin m) : Poly m →ₐ[ℚ] Poly m :=
  substAlgHom (fun j => j ≠ i) (fun _ => 1)

@[simp] theorem evalAtOne_X {m : ℕ} (i j : Fin m) :
    evalAtOne i (X j) = if j = i then 1 else X j := by
  simp [evalAtOne, substAlgHom, substFn]

theorem evalAtOne_comm {m : ℕ} (i j : Fin m) (p : Poly m) :
    evalAtOne i (evalAtOne j p) = evalAtOne j (evalAtOne i p) := by
  have h : (evalAtOne i).comp (evalAtOne j) = (evalAtOne j).comp (evalAtOne i) := by
    by_cases hij : i = j
    · subst j; rfl
    apply MvPolynomial.algHom_ext
    intro t
    by_cases hti : t = i
    · subst t; simp [hij]
    by_cases htj : t = j
    · subst t; simp [Ne.symm hij]
    simp [hti, htj]
  exact congrArg (fun f : Poly m →ₐ[ℚ] Poly m => f p) h

theorem pderiv_evalAtOne {m : ℕ} (i j : Fin m) (hij : j ≠ i) (p : Poly m) :
    pderiv j (evalAtOne i p) = evalAtOne i (pderiv j p) :=
  pderiv_piSubst_kept (fun t => t ≠ i) (fun _ => 1) hij p

/-- A complementary-coordinate branch. -/
noncomputable def localA {m : ℕ} (i : Fin m) : Poly m →ₗ[ℚ] Poly m where
  toFun p := -(1 - X i) * evalAtOne i (pderiv i p)
  map_add' p q := by simp [mul_add]
  map_smul' a p := by simp [Algebra.smul_def, mul_left_comm]

/-- A selected-coordinate branch. -/
noncomputable def localB {m : ℕ} (i : Fin m) : Poly m →ₗ[ℚ] Poly m where
  toFun p := (2 * X i - 1) * evalAtOne i p
  map_add' p q := by simp [mul_add]
  map_smul' a p := by simp [Algebra.smul_def, mul_left_comm]

@[simp] theorem localA_apply {m : ℕ} (i : Fin m) (p : Poly m) :
    localA i p = -(1 - X i) * evalAtOne i (pderiv i p) := rfl

@[simp] theorem localB_apply {m : ℕ} (i : Fin m) (p : Poly m) :
    localB i p = (2 * X i - 1) * evalAtOne i p := rfl

theorem evalAtOne_localA {m : ℕ} (i j : Fin m) (hij : i ≠ j) (p : Poly m) :
    evalAtOne i (localA j p) = localA j (evalAtOne i p) := by
  simp only [localA_apply, map_mul, map_neg, map_sub, map_one, evalAtOne_X,
    if_neg (Ne.symm hij), pderiv_evalAtOne i j (Ne.symm hij)]
  rw [evalAtOne_comm]

theorem evalAtOne_localB {m : ℕ} (i j : Fin m) (hij : i ≠ j) (p : Poly m) :
    evalAtOne i (localB j p) = localB j (evalAtOne i p) := by
  simp only [localB_apply, map_mul, map_sub, map_one, map_ofNat, evalAtOne_X,
    if_neg (Ne.symm hij)]
  rw [evalAtOne_comm]

theorem pderiv_localA {m : ℕ} (i j : Fin m) (hij : i ≠ j) (p : Poly m) :
    pderiv i (localA j p) = localA j (pderiv i p) := by
  simp only [localA_apply, pderiv_mul, map_neg, map_sub, pderiv_one,
    pderiv_X_of_ne (Ne.symm hij), sub_self, neg_zero, zero_mul, zero_add,
    pderiv_evalAtOne j i hij]
  rw [IterDerivHelpers.pderiv_comm]

theorem pderiv_localB {m : ℕ} (i j : Fin m) (hij : i ≠ j) (p : Poly m) :
    pderiv i (localB j p) = localB j (pderiv i p) := by
  have hconst : pderiv i (2 : Poly m) = 0 := by
    rw [show (2 : Poly m) = C 2 by simp [map_ofNat], pderiv_C]
  simp only [localB_apply, pderiv_mul, map_sub, pderiv_one, hconst,
    pderiv_X_of_ne (Ne.symm hij), zero_mul, mul_zero, add_zero, sub_zero,
    zero_add, pderiv_evalAtOne j i hij]

theorem localA_comm {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    localA i * localA j = localA j * localA i := by
  apply LinearMap.ext
  intro p
  change localA i (localA j p) = localA j (localA i p)
  simp only [localA_apply, pderiv_mul]
  simp only [map_neg, map_sub, pderiv_one, pderiv_X_of_ne hij, sub_self,
    pderiv_X_of_ne (Ne.symm hij), neg_zero, zero_mul, zero_add,
    pderiv_evalAtOne i j (Ne.symm hij), pderiv_evalAtOne j i hij]
  simp only [map_mul, map_neg, map_sub, map_one, evalAtOne_X,
    if_neg hij, if_neg (Ne.symm hij)]
  rw [IterDerivHelpers.pderiv_comm, evalAtOne_comm]
  ring

theorem localA_localB_comm {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    localA i * localB j = localB j * localA i := by
  apply LinearMap.ext
  intro p
  change localA i (localB j p) = localB j (localA i p)
  rw [localA_apply, pderiv_localB i j hij, evalAtOne_localB i j hij]
  simp only [localA_apply, localB_apply, map_mul, map_neg, map_sub, map_one,
    evalAtOne_X, if_neg hij]
  rw [evalAtOne_comm]
  ring

theorem localB_comm {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    localB i * localB j = localB j * localB i := by
  apply LinearMap.ext
  intro p
  change localB i (localB j p) = localB j (localB i p)
  rw [localB_apply, evalAtOne_localB i j hij]
  simp only [localB_apply, map_mul, map_sub, map_one, map_ofNat,
    evalAtOne_X, if_neg hij]
  rw [evalAtOne_comm]
  ring

/-- The exact designated projected row factors used by the bilinear kernel. -/
theorem qRow_factorization {m : ℕ} (S : Finset (Fin m)) :
    GodMoveDesignatedPositiveBoundary.qRow S =
      (∏ i ∈ S, (2 * X i - 1 : Poly m)) *
        ∏ i ∈ Finset.univ \ S, (1 - X i : Poly m) := by
  have h := GodMoveQuadraticSheetLift.projected_row_factorization S (1 : Poly m) (by simp)
  simp only [one_mul] at h
  rw [GodMoveDesignatedComplementRows.mlProj_pderiv_boolFactor_prod] at h
  simp only [SymmetricPower.pderiv_boolFactor_self] at h
  change MultilinearSPDP.mlProj (SymmetricPower.boolFactorDerivProd S) = _
  rw [h]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring

end GodMoveGaugeLocalOperators

#print axioms GodMoveGaugeLocalOperators.evalAtOne_comm
#print axioms GodMoveGaugeLocalOperators.pderiv_evalAtOne
#print axioms GodMoveGaugeLocalOperators.localA_comm
#print axioms GodMoveGaugeLocalOperators.localA_localB_comm
#print axioms GodMoveGaugeLocalOperators.localB_comm
#print axioms GodMoveGaugeLocalOperators.qRow_factorization
