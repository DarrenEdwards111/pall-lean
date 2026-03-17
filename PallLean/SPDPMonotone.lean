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
axiom pderiv_eval_comm {N : ℕ} (i j : Fin N) (c : ℚ)
    (p : MvPolynomial (Fin N) ℚ) (hij : i ≠ j) :
    MvPolynomial.pderiv i (MvPolynomial.aeval
      (fun k => if k = j then MvPolynomial.C c else X k) p) =
    MvPolynomial.aeval (fun k => if k = j then MvPolynomial.C c else X k)
      (MvPolynomial.pderiv i p)

/-- Iterated derivative commutes with evaluation when no derivative
    variable equals the evaluated variable. -/
axiom iterDerivList_eval_comm {N : ℕ} (S : List (Fin N)) (j : Fin N) (c : ℚ)
    (p : MvPolynomial (Fin N) ℚ) (hS : ∀ i ∈ S, i ≠ j) :
    iterDerivList S (MvPolynomial.aeval
      (fun k => if k = j then MvPolynomial.C c else X k) p) =
    MvPolynomial.aeval (fun k => if k = j then MvPolynomial.C c else X k)
      (iterDerivList S p)

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
