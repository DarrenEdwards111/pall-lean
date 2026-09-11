import GodMoveCircuitNormalization

/-!
# Interpolation through a finite state partition

A Boolean output determined by a finite state classification is a linear
combination of the characteristic polynomials of its state fibers. The
identity follows directly from the existing finite interpolation sum.

This is a polynomial identity, not a construction-time or derivative-rank
bound. A small family of output-state indicators need not contain their
partial derivatives.
-/

namespace GodMoveFiniteStateInterpolation

open GodMoveBooleanInterpolation
open scoped BigOperators

variable {L : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

/-- An output depending only on a finite state classification is the weighted
sum of the interpolated fibers of that actual classification. -/
theorem interpolate_comp_eq_sum_fibers
    (f : Assignment L → α) (accept : α → Bool) :
    interpolate (fun x => accept (f x)) =
      ∑ s : α, bit (accept s) • interpolate (fun x => decide (f x = s)) := by
  classical
  simp_rw [interpolate_eq_weighted_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (f x)]
  · cases accept (f x) <;> simp [bit]
  · intro s _ hne
    simp [Ne.symm hne]
  · simp

/-- The interpolated constant-true function is the constant polynomial one. -/
theorem interpolate_true_eq_one (L : ℕ) :
    interpolate (fun _ : Assignment L => true) = 1 := by
  apply GodMoveCircuitNormalization.multilinear_eq_of_boolean_eval _ _
    (interpolate_isMultilinear _)
  · intro a ha i
    exact (MvPolynomial.degreeOf_le_iff.mp
      (show (1 : Poly L).degreeOf i ≤ 1 by simp)) a ha
  · intro x
    simp [eval_interpolate, bit]

/-- The state fibers partition the entire Boolean input space. -/
theorem sum_fibers_eq_one (f : Assignment L → α) :
    (∑ s : α, interpolate (fun x => decide (f x = s))) = 1 := by
  have h := interpolate_comp_eq_sum_fibers f (fun _ => true)
  simpa only [bit, Bool.true_eq, ↓reduceIte, one_smul, interpolate_true_eq_one] using h.symm

end GodMoveFiniteStateInterpolation

#print axioms GodMoveFiniteStateInterpolation.interpolate_comp_eq_sum_fibers
#print axioms GodMoveFiniteStateInterpolation.interpolate_true_eq_one
#print axioms GodMoveFiniteStateInterpolation.sum_fibers_eq_one
