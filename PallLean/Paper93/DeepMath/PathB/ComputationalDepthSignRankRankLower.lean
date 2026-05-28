import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSignRankInvariant
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith

/-!
# Ordinary-rank route for small unconditional sign-rank lower bounds

This file is a deliberately modest companion to
`ComputationalDepthSignRankInvariant.lean`.

The main reusable point is that a `HasSignRankLE M d` witness produces an
ordinary real matrix with the same sign pattern and matrix rank at most `d`.
Therefore any ordinary-rank lower bound holding for every real sign-realizer
can be fed into the same depth-2 conservation interface as a sign-rank lower
bound.

The concrete unconditional example here is only the `2 × 2` sign-nonsingular
pattern

```
  +  +
  +  -
```

Every real matrix with this sign pattern has negative determinant, hence rank
`2`.  This is not a Forster-scale theorem; it is a small axiom-free lower-bound
route that is compatible with the existing invariant kernel.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Matrix

/-! ## Rank interface for sign-realizers -/

/-- A real matrix realizes the Boolean sign pattern `M` when every entry has
strictly the requested sign. -/
def SignRealizes {m n : Nat} (M : Fin m -> Fin n -> Bool)
    (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i j, 0 < sgn (M i j) * A i j

/-- Any matrix product through an inner dimension `d` has ordinary matrix rank
at most `d`. -/
theorem matrix_rank_mul_le_inner {m n d : Nat}
    (B : Matrix (Fin m) (Fin d) ℝ) (C : Matrix (Fin d) (Fin n) ℝ) :
    (B * C).rank <= d := by
  exact le_trans (Matrix.rank_mul_le_left B C) (Matrix.rank_le_width B)

/-- A `HasSignRankLE M d` witness yields a concrete real sign-realizer of
ordinary rank at most `d`. -/
theorem exists_signRealizer_rank_le_of_hasSignRankLE {m n d : Nat}
    {M : Fin m -> Fin n -> Bool} (h : HasSignRankLE M d) :
    ∃ A : Matrix (Fin m) (Fin n) ℝ, SignRealizes M A ∧ A.rank <= d := by
  obtain ⟨B, C, hBC⟩ := h
  exact ⟨B * C, hBC, matrix_rank_mul_le_inner B C⟩

/-- Ordinary-rank lower-bound predicate: every real sign-realizer of `M` has
rank at least `B`. -/
def OrdinaryRankLowerBound {m n : Nat} (M : Fin m -> Fin n -> Bool)
    (B : Nat) : Prop :=
  ∀ A : Matrix (Fin m) (Fin n) ℝ, SignRealizes M A -> B <= A.rank

/-- Ordinary-rank lower bounds imply the sign-rank lower-bound shape consumed
by `ComputationalDepthSignRankInvariant.lean`. -/
theorem signRankLowerBound_of_ordinaryRankLowerBound {m n B : Nat}
    {M : Fin m -> Fin n -> Bool}
    (hR : OrdinaryRankLowerBound M B) : ForsterLowerBound M B := by
  intro d hLE
  obtain ⟨A, hA, hrank⟩ := exists_signRealizer_rank_le_of_hasSignRankLE hLE
  exact le_trans (hR A hA) hrank

/-- Depth-2 budget lower bound from an ordinary-rank lower bound, with no
analytic Forster input. -/
theorem depth2_budget_ge_of_ordinaryRankLowerBound {m n : Nat}
    {M : Fin m -> Fin n -> Bool} {B : Nat}
    (Compute : Nat -> Prop) (bound : Nat -> Nat)
    (hR : OrdinaryRankLowerBound M B)
    (hbridge : ∀ s, Compute s -> HasSignRankLE M (bound s))
    {s : Nat} (hs : Compute s) : B <= bound s :=
  depth2_budget_ge Compute bound
    (signRankLowerBound_of_ordinaryRankLowerBound hR) hbridge hs

/-- Conservation no-go using an ordinary-rank lower bound in place of a carried
Forster lower bound. -/
theorem no_small_depth2_of_ordinaryRankLowerBound {m n : Nat}
    {M : Fin m -> Fin n -> Bool} {B : Nat}
    (Compute : Nat -> Prop) (bound : Nat -> Nat)
    (hR : OrdinaryRankLowerBound M B)
    (hbridge : ∀ s, Compute s -> HasSignRankLE M (bound s))
    {s : Nat} (hs : Compute s) (hsmall : bound s < B) : False :=
  Nat.not_lt.mpr
    (depth2_budget_ge_of_ordinaryRankLowerBound Compute bound hR hbridge hs)
    hsmall

/-! ## A concrete `2 × 2` sign-nonsingular pattern -/

/-- The `2 × 2` pattern with a single negative bottom-right entry:
`(+,+; +,-)`. -/
def checker2 (i j : Fin 2) : Bool :=
  if i = 1 ∧ j = 1 then false else true

@[simp] theorem checker2_00 : checker2 0 0 = true := by
  decide

@[simp] theorem checker2_01 : checker2 0 1 = true := by
  decide

@[simp] theorem checker2_10 : checker2 1 0 = true := by
  decide

@[simp] theorem checker2_11 : checker2 1 1 = false := by
  decide

/-- Every real matrix realizing `checker2` has negative determinant. -/
theorem checker2_det_neg_of_signRealizes
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : SignRealizes checker2 A) :
    A.det < 0 := by
  have h00 : 0 < A 0 0 := by
    have h := hA 0 0
    simpa [SignRealizes, sgn] using h
  have h01 : 0 < A 0 1 := by
    have h := hA 0 1
    simpa [SignRealizes, sgn] using h
  have h10 : 0 < A 1 0 := by
    have h := hA 1 0
    simpa [SignRealizes, sgn] using h
  have h11 : A 1 1 < 0 := by
    have h := hA 1 1
    simpa [SignRealizes, sgn] using h
  have hdiag : A 0 0 * A 1 1 < 0 :=
    mul_neg_of_pos_of_neg h00 h11
  have hoff : 0 < A 0 1 * A 1 0 :=
    mul_pos h01 h10
  rw [Matrix.det_fin_two]
  linarith

/-- Every real matrix realizing `checker2` has ordinary rank exactly `2`. -/
theorem checker2_rank_eq_two_of_signRealizes
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : SignRealizes checker2 A) :
    A.rank = 2 := by
  have hdet_neg : A.det < 0 := checker2_det_neg_of_signRealizes A hA
  have hdet_ne : A.det ≠ 0 := ne_of_lt hdet_neg
  have hdet_unit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet_ne
  have hA_unit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hdet_unit
  have hrank : A.rank = Fintype.card (Fin 2) :=
    Matrix.rank_of_isUnit A hA_unit
  simpa using hrank

/-- The concrete ordinary-rank lower bound for `checker2`. -/
theorem checker2_ordinaryRankLowerBound :
    OrdinaryRankLowerBound checker2 2 := by
  intro A hA
  rw [checker2_rank_eq_two_of_signRealizes A hA]

/-- The same concrete lower bound in the existing sign-rank lower-bound shape. -/
theorem checker2_signRankLowerBound : ForsterLowerBound checker2 2 :=
  signRankLowerBound_of_ordinaryRankLowerBound checker2_ordinaryRankLowerBound

/-- No dimension `< 2` factorization can realize the `checker2` sign pattern. -/
theorem checker2_no_hasSignRankLE_lt_two {d : Nat}
    (hLE : HasSignRankLE checker2 d) (hd : d < 2) : False :=
  Nat.not_lt.mpr (checker2_signRankLowerBound d hLE) hd

/-- The depth-2 conservation no-go specialized to the explicit `checker2`
ordinary-rank lower bound. -/
theorem no_small_depth2_checker2
    (Compute : Nat -> Prop) (bound : Nat -> Nat)
    (hbridge : ∀ s, Compute s -> HasSignRankLE checker2 (bound s))
    {s : Nat} (hs : Compute s) (hsmall : bound s < 2) : False :=
  no_small_depth2_of_ordinaryRankLowerBound Compute bound
    checker2_ordinaryRankLowerBound hbridge hs hsmall

/-! ## Kernel-only trace -/

#print axioms matrix_rank_mul_le_inner
#print axioms exists_signRealizer_rank_le_of_hasSignRankLE
#print axioms signRankLowerBound_of_ordinaryRankLowerBound
#print axioms checker2_ordinaryRankLowerBound
#print axioms no_small_depth2_checker2

end PallLean.Paper93.DeepMath.PathB
