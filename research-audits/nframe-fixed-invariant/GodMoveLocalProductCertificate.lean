import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring

/-!
# An explicit algebraic product certificate from local equations

This construction does not place the full product among the source equations.
Its generators are only `w_0 - 1` and `w_(i+1) - w_i * f_i`.
An explicit telescoping identity derives the output relation
`w_n - product_(i<n) f_i` as a polynomial combination of these generators.
The identity holds in every commutative ring, without division or a nonzero
factor premise, and hence applies to actual multivariate polynomials.

This is ideal membership / algebraic elimination, not a rank-monotone
linear projection of the additive constraint energy. The displayed
certificate exposes the products needed as multipliers. Their complexity
cannot be omitted from a proposed SPDP transport argument. No polynomial
P-side rank bound, common-span collapse, or SAT separation is asserted.
-/

namespace GodMoveLocalProductCertificate

open scoped BigOperators

variable {R : Type*} [CommRing R]

def initialResidual (w : ℕ → R) : R := w 0 - 1

def stepResidual (f w : ℕ → R) (i : ℕ) : R := w (i + 1) - w i * f i

/-- The source ideal contains only the initial equation and local steps. -/
def localConstraintIdeal (f w : ℕ → R) (n : ℕ) : Ideal R :=
  Ideal.span {p | p = initialResidual w ∨ ∃ i < n, p = stepResidual f w i}

/-- An explicit multiplier for each local residual is the remaining suffix
product. In particular, the full product is derived, not a source generator. -/
theorem output_relation_certificate (f w : ℕ → R) (n : ℕ) :
    w n - ∏ i ∈ Finset.range n, f i =
      initialResidual w * (∏ i ∈ Finset.range n, f i) +
        ∑ i ∈ Finset.range n,
          stepResidual f w i * (∏ j ∈ Finset.Ico (i + 1) n, f j) := by
  induction n with
  | zero => simp [initialResidual]
  | succ n ih =>
    have hsuffix :
        (∑ i ∈ Finset.range n,
          stepResidual f w i * (∏ j ∈ Finset.Ico (i + 1) (n + 1), f j)) =
        (∑ i ∈ Finset.range n,
          stepResidual f w i * (∏ j ∈ Finset.Ico (i + 1) n, f j)) * f n := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.prod_Ico_succ_top (Finset.mem_range.mp hi) f]
      exact (mul_assoc _ _ _).symm
    rw [Finset.prod_range_succ, Finset.sum_range_succ, hsuffix]
    simp only [Finset.Ico_self, Finset.prod_empty, mul_one]
    calc
      w (n + 1) - (∏ i ∈ Finset.range n, f i) * f n =
          (w n - ∏ i ∈ Finset.range n, f i) * f n + stepResidual f w n := by
            simp only [stepResidual]
            ring
      _ = _ := by rw [ih]; ring

/-- Algebraic elimination derives the product/output equation from the
local source ideal, with no product relation inserted as a generator. -/
theorem output_relation_mem_local_ideal (f w : ℕ → R) (n : ℕ) :
    w n - ∏ i ∈ Finset.range n, f i ∈ localConstraintIdeal f w n := by
  rw [output_relation_certificate]
  apply Ideal.add_mem
  · apply Ideal.mul_mem_right
    exact Ideal.subset_span (Or.inl rfl)
  · apply Submodule.sum_mem
    intro i hi
    apply Ideal.mul_mem_right
    exact Ideal.subset_span (Or.inr ⟨i, Finset.mem_range.mp hi, rfl⟩)

/-- Every assignment satisfying the local equations satisfies the derived
output equation; this corollary retains the explicit algebraic certificate. -/
theorem local_equations_force_product (f w : ℕ → R) (n : ℕ)
    (hinitial : w 0 = 1)
    (hstep : ∀ i < n, w (i + 1) = w i * f i) :
    w n = ∏ i ∈ Finset.range n, f i := by
  have h := output_relation_certificate f w n
  have hsum : (∑ i ∈ Finset.range n,
      stepResidual f w i * (∏ j ∈ Finset.Ico (i + 1) n, f j)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [stepResidual, hstep i (Finset.mem_range.mp hi)]
  rw [hsum] at h
  apply sub_eq_zero.mp
  simpa [initialResidual, hinitial] using h

end GodMoveLocalProductCertificate

#print axioms GodMoveLocalProductCertificate.output_relation_certificate
#print axioms GodMoveLocalProductCertificate.output_relation_mem_local_ideal
#print axioms GodMoveLocalProductCertificate.local_equations_force_product
