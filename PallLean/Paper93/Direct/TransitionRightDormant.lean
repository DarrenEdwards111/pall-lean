/-
  PallLean/Paper93/Direct/TransitionRightDormant.lean

  Paper §251 dormancy — vacuous discharge of the `transitionRight`
  case for the canonical Cook-Levin constraint-type map.

  Agent M16 (parallel).

  ## Scope

  The canonical concrete constraint-type map on the Cook-Levin factor
  list,

      WithinProfileBound.cookLevinConstraintType M n hn htb hns
          : Fin (cookLevinFactorList M n hn htb hns).length
              → SymmetricPowerBound.ConstraintType,

  is defined by a three-way `if`-cascade that returns exactly one of
  `booleanity`, `adjacency`, or `transitionLeft`. The ambient
  `ConstraintType.transitionRight` coordinate is dormant on the
  compiled Cook-Levin family in the sense of paper §251: no factor
  index ever maps to `transitionRight` under the canonical type map.

  This file delivers the direct vacuity statement needed by the
  per-type spanning composition: if some index `i` satisfied
  `cookLevinConstraintType M n hn htb hns i = ConstraintType.transitionRight`,
  we would derive `False`. Consequently any obligation to span, bound,
  or otherwise account for `transitionRight` row contributions is
  vacuously discharged, and the corresponding row contribution is
  trivially `0` inside any submodule via `Submodule.zero_mem`.

  ## Deliverables

    * `transitionRight_vacuous` — for every Turing-machine parameter
      tuple `(M, n, hn, htb, hns)` with `hn4 : n ≥ 4` and every bounded
      profile `bp : BoundedProfile (Nat.log 2 n)`, no factor index
      `i` satisfies
      `cookLevinConstraintType M n hn htb hns i = ConstraintType.transitionRight`.
      (The `hn4` and `bp` arguments are part of the standard tuple
      signature used by the parallel Direct agents; the vacuity
      statement itself does not depend on their particular values.)

    * `transitionRight_row_zero_mem` — a direct corollary: if the
      canonical type of `i` is `transitionRight`, then the zero row
      contribution lies in any submodule of `MvPolynomial (Fin n) ℚ`.
      This is immediate from `Submodule.zero_mem` once the hypothesis
      is refuted; we package it for downstream callers that need the
      membership shape rather than the refutation shape.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/

import PallLean.WithinProfileBound

namespace PallLean.Paper93.Direct

open MvPolynomial
open SymmetricPowerBound (ConstraintType)
open TuringMachine (DTM)
open WithinProfileBound

/-- **Paper §251 transitionRight dormancy (vacuous case).**

The canonical concrete constraint-type map on the Cook-Levin factor
list is a three-way cascade returning one of `booleanity`, `adjacency`,
or `transitionLeft`. Therefore no factor index `i` is ever classified
as `transitionRight`: the hypothesis
`cookLevinConstraintType M n hn htb hns i = ConstraintType.transitionRight`
is refutable.

This is the direct vacuous-discharge witness for the dormant fourth
`ConstraintType` coordinate on the compiled Cook-Levin family; see the
comments around `WithinProfileBound.cookLevinConstraintType` for the
underlying definition, and §251 of the paper for the dormancy
convention.

The `hn4` and `bp` arguments are present to match the standard
parameter tuple used by the parallel Direct agents (M1, M16, ...);
they are not used inside the proof because the vacuity of the
`transitionRight` case depends only on the shape of the `if`-cascade
defining `cookLevinConstraintType`. -/
theorem transitionRight_vacuous
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4) (bp : BoundedProfile (Nat.log 2 n)) :
    ∀ i : Fin (cookLevinFactorList M n hn htb hns).length,
        cookLevinConstraintType M n hn htb hns i
            = ConstraintType.transitionRight → False := by
  -- `hn4` and `bp` are unused: the vacuity statement depends only on
  -- the `if`-cascade defining `cookLevinConstraintType`.
  intro i hEq
  -- Unfold the canonical type map and perform case analysis on the
  -- two `if` conditions.  In all three branches the returned type is
  -- `booleanity`, `adjacency`, or `transitionLeft` respectively, and
  -- none of those equals `transitionRight`.
  unfold cookLevinConstraintType at hEq
  by_cases h1 : i.1 < n
  · -- Booleanity branch.
    rw [if_pos h1] at hEq
    exact ConstraintType.noConfusion hEq
  · by_cases h2 :
        i.1 < n + (PaperFaithfulSeparation.adjConstraintList n).length
    · -- Adjacency branch.
      rw [if_neg h1, if_pos h2] at hEq
      exact ConstraintType.noConfusion hEq
    · -- transitionLeft branch.
      rw [if_neg h1, if_neg h2] at hEq
      exact ConstraintType.noConfusion hEq

/-- **Direct corollary: dormant `transitionRight` rows contribute `0`
inside any submodule.**

Because the `transitionRight` case is vacuous on the Cook-Levin factor
list (Theorem `transitionRight_vacuous`), the row contribution assigned
to any index of type `transitionRight` is the empty sum, i.e. the zero
element `0 : MvPolynomial (Fin n) ℚ`. This lies in every submodule by
`Submodule.zero_mem`, so the dormant-row obligation is discharged in
the shape consumed by the per-type spanning composition.

The hypothesis
`cookLevinConstraintType M n hn htb hns i = ConstraintType.transitionRight`
is refuted by `transitionRight_vacuous`, so this theorem's body is an
absurd elimination followed by a trivial membership. -/
theorem transitionRight_row_zero_mem
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4) (bp : BoundedProfile (Nat.log 2 n))
    (U : Submodule ℚ (MvPolynomial (Fin n) ℚ)) :
    ∀ i : Fin (cookLevinFactorList M n hn htb hns).length,
      cookLevinConstraintType M n hn htb hns i
          = ConstraintType.transitionRight →
        (0 : MvPolynomial (Fin n) ℚ) ∈ U := by
  intro i hEq
  -- Refute the hypothesis via the vacuity theorem; the conclusion is
  -- then trivial (though unreachable) by `Submodule.zero_mem`.
  exact absurd hEq
    (fun h => transitionRight_vacuous M n hn htb hns hn4 bp i h)

/-! ## Kernel-only axiom trace

The deliverables should depend only on
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms transitionRight_vacuous
#print axioms transitionRight_row_zero_mem

end PallLean.Paper93.Direct
