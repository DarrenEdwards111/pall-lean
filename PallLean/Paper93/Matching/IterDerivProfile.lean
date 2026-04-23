/-
  PallLean/Paper93/Matching/IterDerivProfile.lean

  Agent N4 of N (parallel) — structural computation of the row profile
  of `iterDerivList S factor_i` in terms of the Cook-Levin constraint
  type classification.

  ## Scope

  Given N1's `rowProfile` definition in `Paper93/Matching/ProfileMatches`
  (which is the Kronecker indicator at the constraint type of row `i`),
  this file proves a single structural identity: if
  `cookLevinConstraintType M n hn htb hns i = τ`, then the row profile
  at index `i` is exactly `fun τ' => if τ' = τ then 1 else 0`.

  The proof is purely definitional/structural: unfold `rowProfile`,
  rewrite using the hypothesis `hτ`, and collapse the `if`-equality
  via symmetry of equality.

  No auxiliary content; no rank, finrank, or spanning claims.

  Kernel-only: this file introduces one theorem and no axioms.
-/

import PallLean.Paper93.Matching.ProfileMatches

namespace PallLean.Paper93.Matching

open SymmetricPowerBound TuringMachine MvPolynomial

/-- **Agent N4 structural identity.**

For any factor index `i` in the compiled Cook-Levin factor list whose
constraint type is `τ = cookLevinConstraintType M n hn htb hns i`, the
row profile of `iterDerivList S factor_i` at shift `shift` is the
Kronecker indicator at `τ`:
`rowProfile … i = fun τ' => if τ' = τ then 1 else 0`.

This is a purely structural/definitional statement: unfolding
`rowProfile` yields `if cookLevinConstraintType … i = τ' then 1 else 0`,
which under the hypothesis `hτ : cookLevinConstraintType … i = τ`
collapses to `if τ = τ' then 1 else 0 = if τ' = τ then 1 else 0` by
symmetry of equality. -/
theorem iterDerivList_row_profile
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (i : Fin (WithinProfileBound.cookLevinFactorList M n hn htb hns).length)
    (τ : ConstraintType)
    (hτ : WithinProfileBound.cookLevinConstraintType M n hn htb hns i = τ) :
    rowProfile M n hn htb hns S shift i
      = (fun τ' : ConstraintType => if τ' = τ then 1 else 0) := by
  -- Reduce to pointwise equality of functions.
  funext τ'
  -- Unfold the definition of `rowProfile`.
  unfold rowProfile
  -- After unfolding, the left side is
  --   `if cookLevinConstraintType M n hn htb hns i = τ' then 1 else 0`.
  -- Using `hτ : cookLevinConstraintType … i = τ`, rewrite to
  --   `if τ = τ' then 1 else 0`.
  rw [hτ]
  -- The resulting goal is
  --   `(if τ = τ' then (1 : ℕ) else 0) = (if τ' = τ then 1 else 0)`.
  -- Case on whether `τ' = τ` to collapse both `if`-expressions.
  by_cases h : τ' = τ
  · -- If `τ' = τ`, both branches evaluate to `1`.
    rw [if_pos h]
    rw [if_pos h.symm]
  · -- If `τ' ≠ τ`, both branches evaluate to `0`; use symmetry of `≠`.
    have h' : τ ≠ τ' := fun heq => h heq.symm
    rw [if_neg h']
    rw [if_neg h]

end PallLean.Paper93.Matching
