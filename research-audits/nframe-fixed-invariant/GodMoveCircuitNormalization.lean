import GodMoveBooleanInterpolation
import Mathlib.Combinatorics.Nullstellensatz

/-!
# Coefficient normalization identifies a Boolean circuit's characteristic

The normalizer here sends each monomial exponent to its support indicator,
using the existing squarefree `tagMonomial` basis. It does not enumerate Boolean assignments.
Its denotation is proved equal to the canonical interpolation when the raw
polynomial has the required Boolean values. No efficient normal-form expansion
or derivative-rank transport is asserted by this semantic result.
-/

namespace GodMoveCircuitNormalization

open MvPolynomial MultilinearSPDP
open GodMoveBooleanInterpolation
open scoped BigOperators

noncomputable def normalizeLinearMap (n : ℕ) : Poly n →ₗ[ℚ] Poly n :=
  Finsupp.lmapDomain ℚ ℚ (fun α => SymmetricPower.tagMonomial α.support)

noncomputable def normalize {n : ℕ} (p : Poly n) : Poly n :=
  normalizeLinearMap n p

theorem normalize_add {n : ℕ} (p q : Poly n) :
    normalize (p + q) = normalize p + normalize q :=
  (normalizeLinearMap n).map_add p q

theorem normalize_monomial {n : ℕ} (α : Fin n →₀ ℕ) (c : ℚ) :
    normalize (monomial α c) = monomial (SymmetricPower.tagMonomial α.support) c := by
  change (Finsupp.lmapDomain ℚ ℚ (fun α : Fin n →₀ ℕ =>
    SymmetricPower.tagMonomial α.support)) (AddMonoidAlgebra.lsingle α c) =
      AddMonoidAlgebra.lsingle (SymmetricPower.tagMonomial α.support) c
  rw [Finsupp.lmapDomain_apply, AddMonoidAlgebra.lsingle_apply,
    Finsupp.mapDomain_single]
  simp [AddMonoidAlgebra.lsingle_apply]

theorem normalize_isMultilinear {n : ℕ} (p : Poly n) :
    IsMultilinear (normalize p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
      rw [normalize_monomial]
      intro β hβ i
      have h : β = SymmetricPower.tagMonomial α.support := by
        simpa using support_monomial_subset hβ
      rw [h]
      exact SymmetricPower.tagMonomial_isMultilinear α.support i
  | add p q hp hq =>
      rw [normalize_add]
      intro α hα i
      rcases Finset.mem_union.mp (Finsupp.support_add hα) with h | h
      · exact hp α h i
      · exact hq α h i

theorem eval_normalize {n : ℕ} (p : Poly n) (a : Assignment n) :
    MvPolynomial.eval (booleanPoint a) (normalize p) =
      MvPolynomial.eval (booleanPoint a) p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
      rw [normalize_monomial,
        eval_monomial, eval_monomial]
      congr 1
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hα : α i = 0
      · simp [SymmetricPower.tagMonomial_apply, Finsupp.mem_support_iff, hα]
      · cases ha : a i <;>
          simp [SymmetricPower.tagMonomial_apply, Finsupp.mem_support_iff,
            hα, booleanPoint, bit, ha]
  | add p q hp hq =>
      rw [normalize_add, map_add, map_add, hp, hq]

/-- Boolean values determine a multilinear polynomial over the rationals. -/
theorem multilinear_eq_of_boolean_eval {n : ℕ} (p q : Poly n)
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (heval : ∀ a : Assignment n,
      MvPolynomial.eval (booleanPoint a) p =
        MvPolynomial.eval (booleanPoint a) q) : p = q := by
  classical
  apply sub_eq_zero.mp
  apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset (p - q)
    (fun _ => ({0, 1} : Finset ℚ))
  · intro i
    have hpdeg : p.degreeOf i ≤ 1 := degreeOf_le_iff.mpr (fun α hα => hp α hα i)
    have hqdeg : q.degreeOf i ≤ 1 := degreeOf_le_iff.mpr (fun α hα => hq α hα i)
    have hdeg := (degreeOf_sub_le i p q).trans (max_le hpdeg hqdeg)
    norm_num
    omega
  · intro x hx
    let a : Assignment n := fun i => decide (x i = 1)
    have ha : booleanPoint a = x := by
      funext i
      have hi := hx i
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with hi | hi <;> simp [booleanPoint, a, bit, hi]
    rw [← ha, map_sub, heval a, sub_self]

/-- Exact equality with interpolation is derived from the raw Boolean semantics. -/
theorem normalize_eq_interpolate {n : ℕ} (p : Poly n)
    (f : Assignment n → Bool)
    (heval : ∀ a, MvPolynomial.eval (booleanPoint a) p = bit (f a)) :
    normalize p = interpolate f := by
  apply multilinear_eq_of_boolean_eval _ _ (normalize_isMultilinear p)
    (interpolate_isMultilinear f)
  intro a
  rw [eval_normalize, heval, eval_interpolate]

end GodMoveCircuitNormalization

#print axioms GodMoveCircuitNormalization.normalize_isMultilinear
#print axioms GodMoveCircuitNormalization.eval_normalize
#print axioms GodMoveCircuitNormalization.multilinear_eq_of_boolean_eval
#print axioms GodMoveCircuitNormalization.normalize_eq_interpolate
