import PallLean.ProfileCompression
import Mathlib.Tactic

/-!
# TypeAnonymity — Paper §9.1, Theorem 23

Clause-type anonymity for the Tseitin product:
Two canonical windows with the same profile produce generators
in a common subspace, via a variable permutation that maps one
window's clause variables to the other's while preserving type.

## Paper reference
Definition 18 (Interface-anonymous profiles) and Theorem 23 (Width⇒Rank).
The key claim: RowSpan(R_h) ⊆ V_h, where V_h is the profile space.
-/

namespace TypeAnonymity

open SPDP MultilinearSPDP Tseitin MvPolynomial NPWitness

/-- A clause permutation compatible with two windows of the same profile.
    Maps w's hit clauses to w₀'s hit clauses, and preserves the
    neighborhood type (number of shared variables with hit set). -/
structure ClausePermutation (n κ : ℕ) (w w₀ : CanonicalWindow n κ) where
  /-- The bijection on clauses -/
  toFun : Fin (numClausesAt n) → Fin (numClausesAt n)
  /-- It's a bijection -/
  bijective : Function.Bijective toFun
  /-- Maps hit clauses to hit clauses -/
  maps_hit : ∀ c ∈ w.hitClauses, toFun c ∈ w₀.hitClauses
  /-- Maps non-hit to non-hit -/
  maps_nonhit : ∀ c, c ∉ w.hitClauses → toFun c ∉ w₀.hitClauses

/-- Existence of a clause permutation for same-profile windows.
    Paper: follows from the profile being a histogram — we can match
    clauses type-by-type using any bijection between same-type buckets. -/
axiom clause_perm_exists (n κ : ℕ) (hn : n ≥ 4)
    (w w₀ : CanonicalWindow n κ)
    (h_same : windowProfile w = windowProfile w₀) :
    Nonempty (ClausePermutation n κ w w₀)

/-- A clause permutation lifts to a variable permutation on Fin (npNumVars n).
    Each clause c has a selector selectorAt n c and clause variables.
    The lifted permutation maps selectorAt n c ↦ selectorAt n (σ c)
    and maps clause vars of c to clause vars of σ(c). -/
axiom lift_to_var_perm (n κ : ℕ)
    (w w₀ : CanonicalWindow n κ)
    (σ : ClausePermutation n κ w w₀) :
    ∃ (ρ : Fin (npNumVars n) → Fin (npNumVars n)),
      Function.Bijective ρ ∧
      -- ρ maps w's selectors to w₀'s selectors
      (∀ c ∈ w.hitClauses, ρ (selectorAt n c) = selectorAt n (σ.toFun c)) ∧
      -- rename ρ commutes with iterDerivList in the appropriate sense
      rename ρ (iterDerivList w.selectorList (tseitinPoly ℚ n)) =
        iterDerivList w₀.selectorList (tseitinPoly ℚ n)

/-- The key algebraic consequence: rename maps generators to generators.
    canonicalGenerator w m = rename ρ⁻¹ (canonicalGenerator w₀ (rename ρ m))
    when ρ is the lifted variable permutation. -/
theorem rename_maps_generators (n κ : ℕ) (hn : n ≥ 4)
    (w w₀ : CanonicalWindow n κ)
    (h_same : windowProfile w = windowProfile w₀)
    (m : MvPolynomial (Fin (npNumVars n)) ℚ)
    (hm_deg : m.totalDegree ≤ κ)
    (hm_vars : m.vars ⊆ w.selectorList.toFinset) :
    canonicalGenerator w m ∈
    Submodule.span ℚ { q | ∃ (m' : MvPolynomial (Fin (npNumVars n)) ℚ),
        m'.totalDegree ≤ κ ∧
        m'.vars ⊆ w₀.selectorList.toFinset ∧
        q = canonicalGenerator w₀ m' } := by
  -- Get the clause permutation
  obtain ⟨σ⟩ := clause_perm_exists n κ hn w w₀ h_same
  -- Get the lifted variable permutation
  obtain ⟨ρ, hρ_bij, hρ_sel, hρ_deriv⟩ := lift_to_var_perm n κ w w₀ σ
  -- canonicalGenerator w m = mlProj(m * iterDerivList w.selectors tseitinPoly)
  -- rename ρ (iterDerivList w.selectors tseitinPoly) = iterDerivList w₀.selectors tseitinPoly
  -- So: canonicalGenerator w m = mlProj(m * rename ρ⁻¹ (iterDerivList w₀.selectors tseitinPoly))
  -- = mlProj(m * rename ρ⁻¹ D₀)
  -- We need this in span of {canonicalGenerator w₀ m' | ...}
  -- This requires showing mlProj commutes with rename for injective ρ
  -- and that the resulting polynomial can be expressed in terms of w₀'s generators.
  sorry

end TypeAnonymity
