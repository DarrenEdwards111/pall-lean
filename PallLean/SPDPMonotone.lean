/-
  SPDPMonotone.lean — SPDP Rank Monotonicity under Variable Evaluation

  Key lemma: evaluating (specializing) variables in a polynomial can
  only DECREASE its blocked SPDP rank. This is because:

  1. Each SPDP generator m · ∂^S p specializes to m' · ∂^{S'} p'
     where p' = eval(p, x_i = c_i)
  2. The span of specialized generators ⊆ (image of) the span of
     original generators
  3. Therefore dim(specialized span) ≤ dim(original span)

  This is Theorem 207's "rank-monotone" property at the algebraic level.
-/
import PallLean.SPDPDefs
import PallLean.CompiledPoly
import PallLean.Permanent
import Mathlib.Tactic
import Mathlib.RingTheory.MvPolynomial.Basic

namespace SPDPMonotone

open MvPolynomial SPDP CompiledPoly

/-! ## Variable evaluation preserves SPDP structure

  If we evaluate variable x_j ↦ c in polynomial p, the result p' satisfies:
  ∂_i(eval_j p) = eval_j(∂_i p) for i ≠ j (derivatives commute with eval)
  m' · ∂^S p' = eval_j(m · ∂^S p)    when j ∉ S and j ∉ vars(m)

  This means the SPDP subspace of the evaluated polynomial is the image
  of the original SPDP subspace under the evaluation map. Since evaluation
  is a linear map (on the polynomial ring), the image has dimension ≤
  the original dimension. -/

/-- Evaluation at a single variable: set x_j = c.
    Uses aeval as a ring hom, then converts to linear map. -/
noncomputable def evalAt {N : ℕ} (j : Fin N) (c : ℚ) :
    MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ :=
  (MvPolynomial.aeval (fun i => if i = j then MvPolynomial.C c else X i)).toLinearMap

/-- Partial derivative commutes with evaluation at a different variable.
    ∂_i(p[x_j := c]) = (∂_i p)[x_j := c] when i ≠ j. -/
theorem pderiv_eval_comm {N : ℕ} (i j : Fin N) (c : ℚ)
    (p : MvPolynomial (Fin N) ℚ) (hij : i ≠ j) :
    MvPolynomial.pderiv i (MvPolynomial.aeval
      (fun k => if k = j then MvPolynomial.C c else X k) p) =
    MvPolynomial.aeval (fun k => if k = j then MvPolynomial.C c else X k)
      (MvPolynomial.pderiv i p) := by
  -- Both sides are linear in p, so suffices to check on monomials
  set φ : MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ :=
    MvPolynomial.aeval (fun k : Fin N => if k = j then MvPolynomial.C c else X k)
  -- pderiv i is a derivation, φ is an algebra hom
  -- For X k: pderiv i (X k) = δ_{i,k}
  -- φ(X k) = if k = j then C c else X k
  -- pderiv i (φ(X k)) = if k = j then 0 else δ_{i,k}
  -- φ(pderiv i (X k)) = if i = k then φ(1) else 0 = δ_{i,k}
  -- When i ≠ j: if k = j, both sides are 0 (pderiv i (C c) = 0, and pderiv i (X k) = 0 since k = j ≠ i)
  -- Otherwise both sides equal δ_{i,k} · 1
  -- So they agree on generators ⇒ agree everywhere (by derivation uniqueness)
  -- Use MvPolynomial.derivation_ext or manual induction
  induction p using MvPolynomial.induction_on with
  | C r =>
    simp [MvPolynomial.pderiv_C, map_zero]
  | mul_X p s ih =>
    -- p * X s case: use Leibniz rule
    change MvPolynomial.pderiv i (φ (p * X s)) = φ (MvPolynomial.pderiv i (p * X s))
    rw [map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul]
    simp only [MvPolynomial.aeval_X, map_add, map_mul]
    by_cases his : i = s
    · subst his
      have hφXi : φ (X i) = X i := by simp [φ, MvPolynomial.aeval_X, hij]
      simp only [MvPolynomial.pderiv_X_self, map_one, mul_one, hφXi]
      rw [ih]
    · -- Need: pderiv i (φ (X s)) = φ (pderiv i (X s))
      suffices h : (MvPolynomial.pderiv i) (φ (X s)) = φ ((MvPolynomial.pderiv i) (X s)) by
        rw [ih, h]
      by_cases hsj : s = j
      · subst hsj
        -- φ(X j) = C c, pderiv i (C c) = 0, and pderiv i (X j) = 0 (since i ≠ j)
        simp [φ, MvPolynomial.aeval_X, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X, his, map_zero]
      · -- φ(X s) = X s, so pderiv i (X s) on both sides
        have : φ (X s) = X s := by simp [φ, MvPolynomial.aeval_X, hsj]
        rw [this]
        -- pderiv i (X s) is a constant (0 or 1), and φ fixes constants
        have : MvPolynomial.pderiv i (X s : MvPolynomial (Fin N) ℚ) =
            MvPolynomial.C (if i = s then 1 else 0) := by
          simp [MvPolynomial.pderiv_X, his, Pi.single_eq_of_ne his]
        rw [this, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  | add p q ihp ihq =>
    simp only [map_add, ihp, ihq]

/-- Iterated derivative commutes with evaluation when no derivative
    variable equals the evaluated variable. -/
theorem iterDerivList_eval_comm {N : ℕ} (S : List (Fin N)) (j : Fin N) (c : ℚ)
    (p : MvPolynomial (Fin N) ℚ) (hS : ∀ i ∈ S, i ≠ j) :
    iterDerivList S (MvPolynomial.aeval
      (fun k => if k = j then MvPolynomial.C c else X k) p) =
    MvPolynomial.aeval (fun k => if k = j then MvPolynomial.C c else X k)
      (iterDerivList S p) := by
  induction S generalizing p with
  | nil => simp [iterDerivList]
  | cons a S ih =>
    show iterDerivList S (MvPolynomial.pderiv a
        (MvPolynomial.aeval (fun k => if k = j then MvPolynomial.C c else X k) p)) =
      MvPolynomial.aeval (fun k => if k = j then MvPolynomial.C c else X k)
        (iterDerivList S (MvPolynomial.pderiv a p))
    have ha : a ≠ j := hS a (List.mem_cons_self ..)
    rw [pderiv_eval_comm a j c _ ha]
    exact ih _ (fun i hi => hS i (List.mem_cons_of_mem _ hi))

/-! ## SPDP rank monotonicity under evaluation

  Main theorem: evaluating variables can only decrease blocked SPDP rank.

  If p' = p[x_{j₁} := c₁, ..., x_{jₖ} := cₖ], then
  Γ_{κ,ℓ}(p', B') ≤ Γ_{κ,ℓ}(p, B)

  where B' is the partition B restricted to the remaining variables. -/

/-! ## Combined Permanent Embedding (Theorem 207 Core)

  The permanent polynomial's SPDP rank is bounded by the compiled
  polynomial's SPDP rank. This combines:
  1. Cook-Levin semantic restriction: evaluating auxiliary variables
     in the compiled polynomial recovers the permanent's structure
  2. Evaluation monotonicity: evaluation cannot increase SPDP rank

  Paper reference: Theorem 207 + Section 9 evaluation monotonicity -/

/-! ## Note on Cook-Levin Embedding

  The Cook-Levin embedding axiom (Paper Lemma 206) has been moved to
  CompiledSeparation.lean as part of the unified compiled_separation_axiom.

  This ensures the P-side bound (rank ≤ √n) and the NP-side extraction
  (perm rank ≤ compiled rank) apply to the SAME Cook-Levin CNF.

  The evaluation monotonicity (Paper Lemma 33) remains PROVED in
  SPDPRestrict.lean (freeSpdp_evalOne_le). -/

end SPDPMonotone
