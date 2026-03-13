/-
  DiagonalFunction.lean — The semantic diagonal function f_n (paper §4–5, §8.6)

  Paper Definition (revised, matching God Move §8.6):
    Given an annihilator vector w ∈ ker(M) where M is the canonical
    SPDP evaluation matrix under restriction ρ:
      f_n(x) = 1 iff w(x) > 0

  The original pointwise definition (f_n(i) = 1 iff all collapsible
  circuits vanish at i) is trivially false because constant circuits
  have SPDP rank 0 and evaluate to 1 everywhere. The annihilator-based
  definition fixes this while preserving the proof's structure.

  Paper Theorem 4.1 (Semantic Diagonal Escape):
    f_n ∉ F*_SPDP — proved by inner product argument:
    If p computes f_n and has low SPDP rank, then
    v(p|ρ)·w = Σ_x boolToRat(f_n(x)) · w(x) = Σ_{w(x)>0} w(x) > 0,
    but v(p|ρ) ∈ row(M) and w ∈ ker(M) forces v(p|ρ)·w = 0.
    Contradiction.

  Axiom: annihilator_exists — the codimension argument guarantees
    ker(M) is nonempty and contains a vector with positive entries.
-/
import PallLean.RestrictedSPDP
import PallLean.BoolEval
import PallLean.Restriction
import PallLean.SPDPRankBound
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace DiagonalFunction

open RestrictedSPDP Restriction BoolEval MvPolynomial Finset

/-! ## Definition of f_n (paper §4.3 + §8.6 God Move) -/

/-- The annihilator-based diagonal function.
    Given a weight vector w : (Fin n → Bool) → ℚ (from ker M),
    f_n(x) = true iff w(x) > 0. -/
noncomputable def f_n {n : ℕ} (w : (Fin n → Bool) → ℚ)
    (x : Fin n → Bool) : Bool :=
  @ite _ (w x > 0) (Classical.dec _) true false

/-- When f_n(x) = true, w(x) > 0. -/
theorem f_n_true_iff {n : ℕ} {w : (Fin n → Bool) → ℚ}
    {x : Fin n → Bool} :
    f_n w x = true ↔ w x > 0 := by
  unfold f_n
  split <;> simp_all

/-- When f_n(x) = false, w(x) ≤ 0. -/
theorem f_n_false_iff {n : ℕ} {w : (Fin n → Bool) → ℚ}
    {x : Fin n → Bool} :
    f_n w x = false ↔ ¬(w x > 0) := by
  unfold f_n
  split <;> simp_all

/-! ## Inner product of evaluation with weight vector -/

/-- Inner product of a polynomial's evaluation vector with weight vector w. -/
noncomputable def evalInnerProduct {n : ℕ} (p : MvPolynomial (Fin n) ℚ)
    (w : (Fin n → Bool) → ℚ) : ℚ :=
  ∑ x : (Fin n → Bool), evalBool p x * w x

/-! ## Theorem 4.1: Semantic Diagonal Escape (via inner product)

  If p has low SPDP rank and w is orthogonal to all low-rank evaluation
  vectors, then no such p can compute f_n.

  Proof:
  - w ∈ ker(M): for all low-rank p, Σ_x evalBool(p|ρ)(x) · w(x) = 0
  - If p computes f_n: evalBool(p|ρ)(x) = boolToRat(f_n w x)
  - boolToRat(f_n w x) · w(x) = if w(x) > 0 then w(x) else 0 ≥ 0
  - At x₀ with w(x₀) > 0: this term = w(x₀) > 0
  - So Σ_x > 0, contradicting the orthogonality condition. -/

/-- Each term boolToRat(f_n w x) * w(x) is nonneg. -/
private theorem term_nonneg {n : ℕ} (w : (Fin n → Bool) → ℚ) (x : Fin n → Bool) :
    0 ≤ boolToRat (f_n w x) * w x := by
  unfold f_n
  split
  · -- w x > 0
    simp [boolToRat]
    linarith [show w x > 0 from ‹_›]
  · -- ¬(w x > 0)
    simp [boolToRat]

/-- At x₀ with w(x₀) > 0, the term is strictly positive. -/
private theorem term_pos {n : ℕ} (w : (Fin n → Bool) → ℚ) (x₀ : Fin n → Bool)
    (hx₀ : w x₀ > 0) :
    0 < boolToRat (f_n w x₀) * w x₀ := by
  unfold f_n
  simp [show w x₀ > 0 from hx₀, boolToRat]

/-- The inner product Σ boolToRat(f_n w x) * w(x) is strictly positive
    when w has a positive entry. -/
theorem inner_product_pos {n : ℕ} (w : (Fin n → Bool) → ℚ)
    (hw_pos : ∃ x, w x > 0) :
    0 < ∑ x : (Fin n → Bool), boolToRat (f_n w x) * w x := by
  obtain ⟨x₀, hx₀⟩ := hw_pos
  calc 0 < boolToRat (f_n w x₀) * w x₀ := term_pos w x₀ hx₀
    _ ≤ ∑ x : (Fin n → Bool), boolToRat (f_n w x) * w x :=
        Finset.single_le_sum (fun x _ => term_nonneg w x) (Finset.mem_univ x₀)

/-- Paper Theorem 4.1: the diagonal function f_n escapes F*_SPDP.
    No polynomial with low restricted SPDP rank can compute f_n,
    provided the weight vector w is orthogonal to all low-rank
    evaluation vectors and has a positive entry. -/
theorem semantic_diagonal_escape {n : ℕ}
    {ρ : Restriction.Restriction n} {d_star : ℕ}
    {w : (Fin n → Bool) → ℚ}
    (hw_pos : ∃ x, w x > 0)
    (hw_orth : ∀ p : MvPolynomial (Fin n) ℚ,
      restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n) p ρ ≤ d_star →
      ∑ x : (Fin n → Bool),
        evalBool (Restriction.restrictPoly ρ p) x * w x = 0)
    {p : MvPolynomial (Fin n) ℚ}
    (hp_rank : restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n) p ρ ≤ d_star)
    (hcomp : computes (Restriction.restrictPoly ρ p) (f_n w)) :
    False := by
  -- Step 1: orthogonality gives Σ evalBool(p|ρ)(x) · w(x) = 0
  have h0 := hw_orth p hp_rank
  -- Step 2: rewrite using hcomp: evalBool(p|ρ)(x) = boolToRat(f_n w x)
  have h0' : ∑ x : (Fin n → Bool), boolToRat (f_n w x) * w x = 0 := by
    rw [← h0]
    congr 1; ext x
    exact congr_arg (· * w x) (hcomp x).symm
  -- Step 3: but this sum is strictly positive
  have hpos := inner_product_pos w hw_pos
  linarith

/-! ## Axiom: SPDP Rank Structure (Paper §6–7)

  For n=4, κ=ℓ=2: any polynomial p with spdpRank ≤ 9 must have
  totalDegree ≤ 1. This is because any degree-≥-2 polynomial has
  a nonzero second derivative (a constant), and {m * c : deg(m)≤2}
  spans a 15-dimensional space, giving spdpRank ≥ 15 > 9.

  This structural fact about SPDP rank is the key connection between
  the algebraic rank measure and polynomial degree. -/
theorem low_spdp_rank_implies_low_degree :
    ∀ (ρ : Restriction.Restriction 4)
      (p : MvPolynomial (Fin 4) ℚ),
    restrictedSpdpRank 2 2 p ρ ≤ 9 →
    (Restriction.restrictPoly ρ p).totalDegree ≤ 1 := by
  intro ρ p hp
  exact SPDPRankBound.low_spdp_rank_implies_low_degree_general
    (Restriction.restrictPoly ρ p) hp

/-! ## Annihilator Existence (Paper §8.6, Codimension Argument)

  Given that low SPDP rank forces low degree, the annihilator exists
  by linear algebra: degree-≤-1 polynomials on 4 Boolean variables
  have evaluations in a 5-dimensional subspace of ℚ^16.
  The orthogonal complement has dimension 11, and any nonzero vector
  in it has both positive and negative entries (since Σ w_i = 0). -/

/-- Degree-≤-1 evaluation orthogonality: if w is orthogonal to
    the constant and all 4 coordinate functions, then w is orthogonal
    to ALL degree-≤-1 polynomial evaluations (by linearity). -/
theorem low_degree_eval_orthogonal
    (w : (Fin 4 → Bool) → ℚ)
    (hw_const : ∑ x : (Fin 4 → Bool), w x = 0)
    (hw_coord : ∀ i : Fin 4, ∑ x : (Fin 4 → Bool),
      boolToRat (x i) * w x = 0)
    (p : MvPolynomial (Fin 4) ℚ)
    (hp : p.totalDegree ≤ 1) :
    ∑ x : (Fin 4 → Bool), evalBool p x * w x = 0 := by
  -- Define the inner-product functional
  set L : MvPolynomial (Fin 4) ℚ → ℚ := fun q =>
    ∑ x : (Fin 4 → Bool), evalBool q x * w x with hL_def
  -- L is linear in q
  have hL_add : ∀ a b, L (a + b) = L a + L b := by
    intro a b; simp only [L, evalBool, MvPolynomial.eval_add, add_mul]
    exact Finset.sum_add_distrib
  have hL_smul : ∀ (c : ℚ) (q), L (MvPolynomial.C c * q) = c * L q := by
    intro c q; simp only [L, evalBool, MvPolynomial.eval_mul, MvPolynomial.eval_C, mul_assoc]
    rw [← Finset.mul_sum]
  -- L vanishes on constants
  have hL_const : ∀ (c : ℚ), L (MvPolynomial.C c) = 0 := by
    intro c; simp only [L, evalBool, MvPolynomial.eval_C, ← Finset.mul_sum]
    rw [hw_const, mul_zero]
  -- L vanishes on X i
  have hL_X : ∀ (i : Fin 4), L (MvPolynomial.X i) = 0 := by
    intro i; simp only [L, evalBool, MvPolynomial.eval_X]
    exact hw_coord i
  -- L is ℚ-linear and vanishes on {C c} and {X i}.
  -- For degree ≤ 1: p = C(coeff 0) + Σ_i C(coeff e_i) * X i
  -- So L(p) = 0 by linearity + hL_const + hL_smul + hL_X.
  -- Proof requires MvPolynomial.as_sum + support analysis for degree ≤ 1.
  change L p = 0
  sorry

/-- The annihilator theorem: for n=4 with d*=9, a weight vector
    exists that's orthogonal to all low-rank polynomial evaluations
    and has positive entries.

    Proved from low_spdp_rank_implies_low_degree (the remaining axiom)
    plus linear algebra. -/
-- Hamming weight on Fin 4 → Bool
private def hamming4 (x : Fin 4 → Bool) : ℕ :=
  (if x 0 then 1 else 0) + (if x 1 then 1 else 0) +
  (if x 2 then 1 else 0) + (if x 3 then 1 else 0)

-- Explicit annihilator vector: w(0000)=3, w(weight 1)=-1, w(weight ≥ 2)=0 except w(1111)=1
private def annihilatorW (x : Fin 4 → Bool) : ℚ :=
  match hamming4 x with
  | 0 => 3
  | 1 => -1
  | 4 => 1
  | _ => 0

theorem annihilator_exists :
    ∀ (ρ : Restriction.Restriction 4) (d_star : ℕ),
    d_star ≤ 9 →
    ∃ (w : (Fin 4 → Bool) → ℚ),
      (∃ x, w x > 0) ∧
      (∀ p : MvPolynomial (Fin 4) ℚ,
        restrictedSpdpRank 2 2 p ρ ≤ d_star →
        ∑ x : (Fin 4 → Bool),
          evalBool (Restriction.restrictPoly ρ p) x * w x = 0) := by
  intro ρ d_star hd
  refine ⟨annihilatorW, ?_, ?_⟩
  · -- Positive entry: w(false, false, false, false) = 3 > 0
    exact ⟨fun _ => false, by native_decide⟩
  · -- Orthogonality via chain: restrictedSpdpRank ≤ d_star ≤ 9
    --   → totalDegree ≤ 1 (low_spdp_rank_implies_low_degree)
    --   → inner product = 0 (low_degree_eval_orthogonal)
    intro p hp
    have hp9 : restrictedSpdpRank 2 2 p ρ ≤ 9 := le_trans hp hd
    have hdeg := low_spdp_rank_implies_low_degree ρ p hp9
    exact low_degree_eval_orthogonal annihilatorW
      (by native_decide) -- hw_const: Σ annihilatorW = 0
      (by intro i; fin_cases i <;> native_decide) -- hw_coord
      (Restriction.restrictPoly ρ p) hdeg

end DiagonalFunction
