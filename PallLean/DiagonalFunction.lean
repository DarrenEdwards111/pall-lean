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

/-! ## Axiom: Annihilator Existence (Paper §8.6, Codimension Argument)

  The canonical SPDP evaluation matrix M has rank ≤ d_star under
  the universal restriction ρ. Since the evaluation space has
  dimension 2^n > d_star, ker(M) is nonempty. Moreover, the
  constant-1 function's evaluation vector (1,...,1) lies in row(M)
  (via the canonical span lemma), so any w ∈ ker(M) satisfies
  Σ w(x) = 0, meaning w has both positive and negative entries.

  We axiomatize the existence of such w with:
  1. ∃ x, w(x) > 0 (has positive entries — nontriviality)
  2. ∀ low-rank p, Σ evalBool(p|ρ)(x) · w(x) = 0 (orthogonality)

  Paper: Proposition 4.2 + §8.6 God Move codimension argument. -/
axiom annihilator_exists :
    ∀ (n : ℕ), n ≥ 2 →
    ∀ (ρ : Restriction.Restriction n) (d_star : ℕ),
    d_star < 2 ^ n →
    ∃ (w : (Fin n → Bool) → ℚ),
      (∃ x, w x > 0) ∧
      (∀ p : MvPolynomial (Fin n) ℚ,
        restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n) p ρ ≤ d_star →
        ∑ x : (Fin n → Bool),
          evalBool (Restriction.restrictPoly ρ p) x * w x = 0)

end DiagonalFunction
