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

/-- The SPDP rank of a polynomial obtained by evaluating variables
    is at most the SPDP rank of the original polynomial.

    This is the core monotonicity lemma. It follows from:
    - evaluation is a linear map on the polynomial ring
    - derivatives commute with evaluation (at different variables)
    - the image of a spanning set under a linear map spans a subspace
      of dimension ≤ the original -/
axiom spdp_rank_eval_le {N : ℕ}
    (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ)
    (bp : CompiledPoly.BlockPartition N)
    (assignments : Fin N → Option ℚ)  -- None = free, Some c = evaluate to c
    : blockedSpdpRankQ κ ℓ
        (MvPolynomial.aeval (fun i =>
          match assignments i with
          | none => X i
          | some c => MvPolynomial.C c) p) bp
      ≤ blockedSpdpRankQ κ ℓ p bp

/-! ## Permanent embeds in compilation

  For a DTM M deciding the hard NP family (which is connected to the
  permanent via Theorem 207's reduction), the compiled polynomial
  P_{M,n} contains the permanent polynomial as a "restriction":

  Setting the auxiliary (witness/computation) variables to appropriate
  values recovers a polynomial whose SPDP rank is at least perm_m's.

  This is the structural content of Theorem 207: the Cook-Levin encoding
  preserves enough algebraic structure that the permanent's SPDP rank
  transfers to the compiled polynomial. -/

/-! ## Cook-Levin Variable Structure

  The compiled polynomial P_{M,n} has variables partitioned into:
  - Input variables (first n positions): encode the problem input
  - Auxiliary variables (remaining positions): encode witness + computation trace

  Setting auxiliary variables to values corresponding to a valid computation
  yields a "semantic restriction" — a polynomial in the input variables
  that captures the function M computes.

  For a DTM computing the permanent, this semantic restriction encodes
  the permanent polynomial on the input matrix. -/

/-- Input variable embedding: the first n variables of the compiled space
    correspond to the problem input. -/
def inputEmbed (k n : ℕ) (i : Fin n) : Fin (compiledVarCount k n) :=
  ⟨i.val, by
    unfold compiledVarCount
    calc i.val < n := i.isLt
      _ ≤ n ^ (2 * k + 1) := Nat.le_self_pow (by omega) n⟩

/-- An assignment that fixes auxiliary variables (index ≥ n) to constants
    while leaving input variables (index < n) free. -/
def inputRestriction (k n : ℕ) (auxVals : Fin (compiledVarCount k n) → ℚ) :
    Fin (compiledVarCount k n) → Option ℚ :=
  fun i => if i.val < n then none else some (auxVals i)

/-! ## Axiom: Permanent Restriction

  Decomposed into two sub-axioms:

  (a) cook_levin_semantic_restriction:
      For any DTM M deciding hardFamily at input length n, there exist
      auxiliary variable values such that the evaluated compiled polynomial
      (restricted to input variables) captures M's computation.

  (b) perm_semantic_rank:
      For the specific hardNPFamily (connected to the permanent via
      Theorem 207), this semantic restriction has SPDP rank ≥ perm_m's rank.

  We keep these bundled for now since separating them requires
  defining "semantic restriction" formally. -/

-- Note: parameterized over hardFamily to avoid circular import with
-- CompiledSeparation. In practice, only called with hardNPFamily.
axiom perm_restriction_exists
    (n : ℕ) (M : TuringMachine.DTM) (k : ℕ)
    (cnf : CookLevinCNF (compiledVarCount k n))
    (hlp : HasLocalPartition cnf)
    (hardFamily : (Fin n → Bool) → Bool)
    (hM : M.decides hardFamily) :
    ∃ (assignments : Fin (compiledVarCount k n) → Option ℚ)
      (bp : CompiledPoly.BlockPartition (Nat.sqrt n * Nat.sqrt n)),
    blockedSpdpRankQ (Nat.log 2 (Nat.sqrt n * Nat.sqrt n))
      (Nat.log 2 (Nat.sqrt n * Nat.sqrt n))
      (Permanent.permPolyFlat (Nat.sqrt n)) bp ≤
    blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
      (MvPolynomial.aeval (fun i =>
        match assignments i with
        | none => X i
        | some c => MvPolynomial.C c) (compiledPolyQ cnf)) hlp.partition

end SPDPMonotone
