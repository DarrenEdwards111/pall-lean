import PallLean.Step4Compiler
import PallLean.MlProjFar

/-!
# Canonical Boolean interpolation: an exact semantic polynomial interface

The canonical interpolation of a Boolean function is the sum, over every
Boolean assignment `a`, of its output bit times
`prod_i (if a_i then X_i else 1-X_i)`.

The repository already constructs this polynomial as `Step4Compiler.chi_phi`
and proves Boolean evaluation and multilinearity in section 161.  We reuse
those checked results, expose the literal weighted-sum formula, and prove
that pointwise function equality gives polynomial equality and equality of
the actual strict and inclusive blocked SPDP ranks.

We also construct one common ambient span, independent of the function,
polynomial, partition, or derivative parameters: all squarefree monomials
on the `n` variables.  Every projected SPDP row lies in this span, and its
spanning family and dimension are bounded by `2^n`.  This is an honest
exponential common-span bound, not the missing polynomial bound.

This is a truth-table construction: the summation index has exactly `2^n`
assignments.  That count is not a lower bound on the smallest representation
of every individual function; some interpolants simplify substantially.
Neither this definition nor its semantic correctness supplies an efficient
compiler, a polynomial SPDP upper bound, or a polynomial common span.

The interpolant is not identified with the existing raw gadget-product
compiler.  In particular, equality of Boolean functions transports rank
between their canonical interpolants, not between arbitrary polynomials
which merely agree on Boolean points.  No SAT separation is asserted.
-/

namespace GodMoveBooleanInterpolation

open MvPolynomial MultilinearSPDP
open scoped BigOperators

abbrev Assignment (n : ℕ) := Fin n → Bool

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℚ

def bit (b : Bool) : ℚ := if b then 1 else 0

def booleanPoint {n : ℕ} (a : Assignment n) : Fin n → ℚ := fun i => bit (a i)

/-- Reuse the repository's exact full truth-table interpolation construction. -/
noncomputable def interpolate {n : ℕ} (f : Assignment n → Bool) : Poly n :=
  Step4Compiler.chi_phi f

theorem interpolate_eq_weighted_sum {n : ℕ} (f : Assignment n → Bool) :
    interpolate f = ∑ a : Assignment n,
      (if f a then (1 : Poly n) else 0) *
        ∏ i : Fin n, (if a i then (X i : Poly n) else 1 - X i) := by
  classical
  unfold interpolate Step4Compiler.chi_phi Step4Compiler.boolMonomial
  apply Finset.sum_congr rfl
  intro a _
  cases f a <;> simp

theorem eval_interpolate {n : ℕ} (f : Assignment n → Bool) (a : Assignment n) :
    MvPolynomial.eval (booleanPoint a) (interpolate f) = bit (f a) :=
  Step4Compiler.chi_phi_agrees_with_1SAT f a

theorem interpolate_isMultilinear {n : ℕ} (f : Assignment n → Bool) :
    IsMultilinear (interpolate f) :=
  Step4Compiler.chi_phi_multilinear f

theorem interpolate_totalDegree_le {n : ℕ} (f : Assignment n → Bool) :
    (interpolate f).totalDegree ≤ n :=
  Step4Compiler.chi_phi_totalDegree_le f

theorem interpolate_congr {n : ℕ} {f g : Assignment n → Bool}
    (h : ∀ a, f a = g a) : interpolate f = interpolate g :=
  congrArg interpolate (funext h)

theorem bit_injective : Function.Injective bit := by
  intro a b h
  cases a <;> cases b <;> simp_all [bit]

theorem interpolate_injective {n : ℕ} :
    Function.Injective (interpolate (n := n)) := by
  intro f g h
  funext a
  apply bit_injective
  have heval := congrArg (MvPolynomial.eval (booleanPoint a)) h
  simpa only [eval_interpolate] using heval

theorem interpolate_eq_iff {n : ℕ} (f g : Assignment n → Bool) :
    interpolate f = interpolate g ↔ ∀ a, f a = g a := by
  constructor
  · intro h a
    exact congrFun (interpolate_injective h) a
  · exact interpolate_congr

/-- This compares the same concrete rank definition, partition, and parameters
on two equal canonical interpolation polynomials. -/
theorem interpolated_rank_eq_of_agrees {n : ℕ}
    (B : SPDP.BlockPartition n) (kappa ell : ℕ)
    {f g : Assignment n → Bool} (h : ∀ a, f a = g a) :
    mlBlockedSpdpRank B kappa ell (interpolate f) =
      mlBlockedSpdpRank B kappa ell (interpolate g) := by
  rw [interpolate_congr h]

/-- Polynomial equality also transports the actual inclusive rank. -/
theorem interpolated_inclusive_rank_eq_of_agrees {n : ℕ}
    (B : SPDP.BlockPartition n) (kappa ell : ℕ)
    {f g : Assignment n → Bool} (h : ∀ a, f a = g a) :
    mlBlockedSpdpRankInc B kappa ell (interpolate f) =
      mlBlockedSpdpRankInc B kappa ell (interpolate g) := by
  rw [interpolate_congr h]

/-- Number of assignments in the explicit full truth-table sum. -/
theorem assignment_count (n : ℕ) : Fintype.card (Assignment n) = 2 ^ n := by
  simp [Assignment]

theorem summation_index_card (n : ℕ) :
    (Finset.univ : Finset (Assignment n)).card = 2 ^ n := by
  rw [Finset.card_univ, assignment_count]

/-! ## One universal, explicitly exponential common span -/

/-- The squarefree monomials on all `n` variables.  The same family is used
for every polynomial and every strict or inclusive SPDP parameter choice. -/
noncomputable def universalBasis (n : ℕ) : Finset (Poly n) :=
  MlProjFar.mlMonomialBasis Finset.univ

noncomputable def universalSpan (n : ℕ) : Submodule ℚ (Poly n) :=
  Submodule.span ℚ (↑(universalBasis n) : Set (Poly n))

theorem universalBasis_card_le_two_pow (n : ℕ) :
    (universalBasis n).card ≤ 2 ^ n := by
  simpa [universalBasis] using
    MlProjFar.mlMonomialBasis_card (Finset.univ : Finset (Fin n))

theorem mlProj_mem_universalSpan {n : ℕ} (p : Poly n) :
    mlProj p ∈ universalSpan n := by
  classical
  apply MlProjFar.mlProj_in_span_of_vars_subset (mlProj p) Finset.univ
  · intro a ha
    change a ∈ (Finsupp.filter (fun b => Finsupp.IsMultilinear b) p).support at ha
    rw [Finsupp.support_filter] at ha
    exact (Finset.mem_filter.mp ha).2
  · exact Finset.subset_univ _

theorem strict_subspace_le_universalSpan {n : ℕ}
    (B : SPDP.BlockPartition n) (kappa ell : ℕ) (p : Poly n) :
    mlBlockedSpdpSubspace B kappa ell p ≤ universalSpan n := by
  apply Submodule.span_le.mpr
  rintro q ⟨S, m, _, _, _, _, rfl⟩
  exact mlProj_mem_universalSpan _

theorem inclusive_subspace_le_universalSpan {n : ℕ}
    (B : SPDP.BlockPartition n) (kappa ell : ℕ) (p : Poly n) :
    mlBlockedSpdpSubspaceInc B kappa ell p ≤ universalSpan n := by
  apply Submodule.span_le.mpr
  rintro q ⟨S, m, _, _, _, _, rfl⟩
  exact mlProj_mem_universalSpan _

theorem universalSpan_finrank_le_two_pow (n : ℕ) :
    Module.finrank ℚ (universalSpan n) ≤ 2 ^ n := by
  letI : Module.Finite ℚ (universalSpan n) :=
    Module.Finite.span_of_finite ℚ (Finset.finite_toSet (universalBasis n))
  simpa using MlProjFar.finrank_le_of_vars_bounded
    (universalSpan n) (Finset.univ : Finset (Fin n)) (le_refl _)

/-- Actual strict SPDP rank is bounded using this one common ambient span. -/
theorem strict_rank_le_two_pow {n : ℕ}
    (B : SPDP.BlockPartition n) (kappa ell : ℕ) (p : Poly n) :
    mlBlockedSpdpRank B kappa ell p ≤ 2 ^ n := by
  simpa [mlBlockedSpdpRank] using MlProjFar.finrank_le_of_vars_bounded
    (mlBlockedSpdpSubspace B kappa ell p) (Finset.univ : Finset (Fin n))
    (strict_subspace_le_universalSpan B kappa ell p)

/-- The same common span and the same exponential budget also bound the
inclusive derivative convention. -/
theorem inclusive_rank_le_two_pow {n : ℕ}
    (B : SPDP.BlockPartition n) (kappa ell : ℕ) (p : Poly n) :
    mlBlockedSpdpRankInc B kappa ell p ≤ 2 ^ n := by
  simpa [mlBlockedSpdpRankInc] using MlProjFar.finrank_le_of_vars_bounded
    (mlBlockedSpdpSubspaceInc B kappa ell p) (Finset.univ : Finset (Fin n))
    (inclusive_subspace_le_universalSpan B kappa ell p)

end GodMoveBooleanInterpolation

#print axioms GodMoveBooleanInterpolation.eval_interpolate
#print axioms GodMoveBooleanInterpolation.interpolate_isMultilinear
#print axioms GodMoveBooleanInterpolation.interpolate_eq_iff
#print axioms GodMoveBooleanInterpolation.interpolated_rank_eq_of_agrees
#print axioms GodMoveBooleanInterpolation.interpolated_inclusive_rank_eq_of_agrees
#print axioms GodMoveBooleanInterpolation.assignment_count
#print axioms GodMoveBooleanInterpolation.strict_subspace_le_universalSpan
#print axioms GodMoveBooleanInterpolation.inclusive_subspace_le_universalSpan
#print axioms GodMoveBooleanInterpolation.universalSpan_finrank_le_two_pow
#print axioms GodMoveBooleanInterpolation.strict_rank_le_two_pow
#print axioms GodMoveBooleanInterpolation.inclusive_rank_le_two_pow
