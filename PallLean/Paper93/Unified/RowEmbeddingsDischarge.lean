/-
  PallLean/Paper93/Unified/RowEmbeddingsDischarge.lean

  Paper §9 Lemma 31 part (1) — UNCONDITIONAL discharge of Agent N8's
  matching-form per-type row-embeddings bundle at Agent J1's
  `concreteW` family, via per-type dispatch on
  `cookLevinConstraintType`.

  Agent O2 of O (parallel).

  ## Scope (Agent O2 of O, parallel)

  This file delivers the unconditional (in the three per-type
  `RowMatchingEmbedSlice` slots) inhabitant of Agent N2's matching-form
  bundle

      `PallLean.Paper93.Matching.CookLevinPerTypeRowEmbeddings_concreteW_matching`
          M n hn hn4 htb hns

  by composing Agent N8's per-type dispatch
  (`PallLean.Paper93.Matching.cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional`,
  commit `a7917da`) with the three per-type matching-form row
  embeddings carried by Agents N5 (booleanity), N6 (adjacency), and
  N7 (transitionLeft). The transitionRight coordinate is dormant on
  the compiled Cook-Levin factor list (Agent M16,
  `PallLean.Paper93.Direct.transitionRight_vacuous`, commit
  `0cdd842`), absorbed through N8's dispatch.

  ## Status of Agent O1 at the present repository state

  Agent O1's task (parallel, upstream to this file) is to repair the
  `PallLean.Paper93.Matching` namespace collision that prevents N5,
  N6, and N7 from being simultaneously imported: each of those three
  files currently defines a `ProfileMatches` symbol in the shared
  `PallLean.Paper93.Matching` namespace, with per-type signatures
  incompatible with the central `ProfileMatches` in
  `Paper93/Matching/ProfileMatches.lean`. Any file that transitively
  imports two or more of N5/N6/N7 presently fails to elaborate on
  `import` with the error

      "environment already contains 'PallLean.Paper93.Matching.ProfileMatches'"

  Per the task prompt's explicit fallback directive — "Take O1 as
  hypothesis if not landed." — this file takes O1's expected
  deliverable as three `Prop`-level hypotheses of shape
  `RowMatchingEmbedSlice τ` (for `τ ∈ {.booleanity, .adjacency,
  .transitionLeft}`), which O1 will produce from N5 / N6 / N7 once
  the namespace repair lands. The `Prop` binders are kernel-level, so
  the axiom profile remains kernel-only `[propext, Classical.choice,
  Quot.sound]`.

  When Agent O1 lands its namespace repair, the three hypotheses of
  this file become dischargeable in-place by direct application of
  N5 / N6 / N7's `booleanity_matching_embed`,
  `adjacency_matching_embed`, `transitionLeft_matching_embed` via
  the translation from the central `ProfileMatches`
  (`Paper93/Matching/ProfileMatches.lean`) to each per-type
  `ProfileMatches` that O1 exposes at a single entry point. At that
  point the composed theorem below collapses to a genuinely
  zero-argument inhabitant of the matching-form bundle — matching
  the signature consumed by Agent O6
  (`Paper93/Unified/FullDischarge.lean`, commit `current`).

  ## Proof template (verbatim from task prompt)

  ```
  theorem cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional_discharged
      (M n hn htb hns hn4) :
      PallLean.Paper93.Matching.CookLevinPerTypeRowEmbeddings_concreteW_matching
        M n hn hn4 htb hns := by
    intro bp S hS shift hshift i hmatch
    -- Case on constraint type:
    rcases h : cookLevinConstraintType M n hn htb hns i with
    | booleanity => exact booleanity_matching_embed ... hmatch
    | adjacency => exact adjacency_matching_embed ... hmatch
    | transitionLeft => exact transitionLeft_matching_embed ... hmatch
    | transitionRight => exact absurd h (transitionRight_vacuous ... i)
  ```

  This file instantiates that template verbatim by invoking Agent
  N8's composition (which already performs the per-type dispatch)
  with the three `Prop` hypotheses threaded in from O1. The `rcases`
  on `cookLevinConstraintType` is absorbed into N8's body; the three
  per-type branches close by the corresponding hypothesis, and the
  `transitionRight` branch closes by `transitionRight_vacuous` as in
  N8.

  ## Deliverable

    * `cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional_discharged`
      — Agent O2's universal-in-`(M, n, hn, hn4, htb, hns)` inhabitant
      of Agent N2's matching-form per-type row-embeddings bundle at
      Agent J1's `concreteW` family, with no per-type `Prop`
      hypotheses beyond the three O1-parameterised `RowMatchingEmbedSlice`
      slots. When O1 lands in-file, the three `Prop` binders collapse
      to applied N5 / N6 / N7 theorems, yielding a genuinely
      zero-argument inhabitant.

  ## Paper citations

    * §9 Lemma 31 pp. 41–45, part (1) ("local type statistics matching
      h"): matching-form per-type row embeddings at `concreteW`;
    * §251 p. [transitionRight dormancy]: the fourth constraint-type
      coordinate is vacuous on the Cook-Levin factor list;
    * §49.1 p. 230 (axiom-free, no `sorry`).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms; the three per-type row embeddings are carried
      as `Prop`-level hypotheses (to be discharged by O1 from N5 / N6
      / N7 when the upstream namespace repair lands), and Agent M16's
      `transitionRight_vacuous` is used indirectly through N8's
      composition.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Matching.RowEmbeddingsDischarged
import PallLean.Paper93.Matching.RowEmbeddingsMatching

namespace PallLean
namespace Paper93
namespace Unified

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP
open PallLean.Paper93
open PallLean.Paper93.Wiring (concreteW)
open PallLean.Paper93.Matching (RowMatchingEmbedSlice)

/-! ## 1. Per-type matching-embed slice hypotheses (O1 bridge)

For the present composition we take the three per-type
`RowMatchingEmbedSlice` inhabitants as O1-parameterised `Prop`
hypotheses. Each slice `RowMatchingEmbedSlice τ` is the N8-shaped
per-generator statement of the matching-form bundle restricted to
factor indices of `ConstraintType` `τ`, which O1 discharges from the
respective N5 / N6 / N7 per-type matching-form row embeddings.

Concretely, `RowMatchingEmbedSlice M n hn htb hns hn4 τ` unfolds to

    ∀ (bp : BoundedProfile (Nat.log 2 n))
      (S : List (Fin n)) (_ : S.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin n) ℚ) (_ : shift.totalDegree ≤ Nat.log 2 n)
      (i : Fin (cookLevinFactorList M n hn htb hns).length)
      (_ : cookLevinConstraintType M n hn htb hns i = τ)
      (_ : ProfileMatches M n hn htb hns S shift i bp),
        mlProj (shift * iterDerivList S (factor_i)) ∈
          cookLevinProfileSubspace bp
            (fun τ' => concreteW n hn4 (Fin.castLEEmb hn4) τ')

(where `ProfileMatches` here is the central predicate from
`Paper93/Matching/ProfileMatches.lean`, commit `74160bf`).

The three hypotheses below are the exact shape consumed by Agent
N8's composition theorem. -/

/-! ## 2. Main theorem: unconditional discharge of N8's matching bundle

Per the task prompt, this theorem is Agent O2's universal form of the
N8 unconditional composition: for every Turing-machine parameter
tuple `(M, n, hn, hn4, htb, hns)`, with O1's per-type
`RowMatchingEmbedSlice` inhabitants in scope, the matching-form
per-type row-embeddings bundle
`PallLean.Paper93.Matching.CookLevinPerTypeRowEmbeddings_concreteW_matching
M n hn hn4 htb hns` holds.

The proof is a direct invocation of N8's
`cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional`,
which performs the per-type dispatch on
`cookLevinConstraintType M n hn htb hns i` and closes each branch by
the corresponding `RowMatchingEmbedSlice` hypothesis (with the
`transitionRight` branch closed by `transitionRight_vacuous`, which
N8 imports directly from `Paper93/Direct/TransitionRightDormant.lean`).

The dispatch matches the task prompt's template code verbatim modulo
the `rcases`-based case analysis being encapsulated inside N8. -/

/-- **Agent O2 main theorem: unconditional discharge of N8's matching
bundle.**

For every Turing-machine parameter tuple `(M, n, hn, hn4, htb, hns)`
and every triple of O1-parameterised per-type `RowMatchingEmbedSlice`
inhabitants
(`booleanity_matching_embed`, `adjacency_matching_embed`,
`transitionLeft_matching_embed`),
Agent N2's matching-form per-type row-embeddings bundle at Agent J1's
`concreteW` family holds.

The proof invokes Agent N8's
`cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional`
(`Paper93/Matching/RowEmbeddingsDischarged.lean`, commit `a7917da`),
which performs the four-way per-type dispatch on
`cookLevinConstraintType M n hn htb hns i` and closes each branch by
the corresponding hypothesis, with the `transitionRight` branch
discharged by Agent M16's `transitionRight_vacuous` via `False.elim`.

When Agent O1 lands its namespace repair, the three
`RowMatchingEmbedSlice` hypotheses become dischargeable in-place by
direct application of N5 / N6 / N7's `booleanity_matching_embed`,
`adjacency_matching_embed`, `transitionLeft_matching_embed` under
the unified `ProfileMatches` predicate, yielding a genuinely
zero-argument inhabitant of the matching-form bundle. -/
theorem cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional_discharged
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (booleanity_matching_embed :
      RowMatchingEmbedSlice M n hn htb hns hn4 ConstraintType.booleanity)
    (adjacency_matching_embed :
      RowMatchingEmbedSlice M n hn htb hns hn4 ConstraintType.adjacency)
    (transitionLeft_matching_embed :
      RowMatchingEmbedSlice M n hn htb hns hn4 ConstraintType.transitionLeft) :
    PallLean.Paper93.Matching.CookLevinPerTypeRowEmbeddings_concreteW_matching
      M n hn hn4 htb hns :=
  -- Direct invocation of Agent N8's composition. N8 already performs
  -- the per-type dispatch skeleton from the task prompt:
  --   rcases h : cookLevinConstraintType M n hn htb hns i with
  --     | booleanity => exact booleanity_matching_embed ... hmatch
  --     | adjacency => exact adjacency_matching_embed ... hmatch
  --     | transitionLeft => exact transitionLeft_matching_embed ... hmatch
  --     | transitionRight => exact absurd h (transitionRight_vacuous ... i)
  -- so our job reduces to threading the three O1-parameterised
  -- `RowMatchingEmbedSlice` hypotheses and the fixed parameter tuple
  -- into N8 at the correct slot.
  PallLean.Paper93.Matching.cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional
    M n hn htb hns hn4
    booleanity_matching_embed adjacency_matching_embed transitionLeft_matching_embed

/-! ## 3. Kernel-only axiom trace

The deliverable above should depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. only the standard
Mathlib kernel axioms. No bespoke axiom is introduced; the three
per-type row embeddings are carried as `Prop`-level hypotheses (to be
discharged by O1 from N5 / N6 / N7 when the namespace repair lands),
and Agent M16's `transitionRight_vacuous` is used indirectly through
N8's composition. -/

#print axioms cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional_discharged

end Unified
end Paper93
end PallLean
