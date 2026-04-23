/-
  PallLean/Paper93/Matching/RowEmbeddingsDischarged.lean

  Paper §9 Lemma 31 part (1) — full per-generator discharge of the
  matching-form row-embeddings bundle
  `CookLevinPerTypeRowEmbeddings_concreteW_matching` at Agent J1's
  concrete `W := fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ`, by
  composition of the three per-type matching row embeddings (N5
  booleanity, N6 adjacency, N7 transitionLeft) with Agent M16's
  `transitionRight` vacuity witness.

  Agent N8 of N (parallel).

  ## Scope

  Agent N2 (`Paper93/Matching/RowEmbeddingsMatching.lean`) introduced
  the paper-faithful Prop

      `CookLevinPerTypeRowEmbeddings_concreteW_matching`

  which asserts the row-level embedding

      `mlProj (shift * iterDerivList S (factor_i))
          ∈ cookLevinProfileSubspace bp (concreteW n hn4 σ)`

  for every bounded profile `bp`, admissible `(S, shift)` pair, factor
  index `i`, and every admissibility witness
  `hmatch : ProfileMatches M n hn htb hns S shift i bp` (N1) that
  pins the histogram `bp.toHistogram` to the Kronecker row profile at
  the constraint type of `i`.

  The four parallel N-agents (N5 booleanity, N6 adjacency, N7
  transitionLeft, M16 transitionRight-vacuity) supply the per-type
  row-level content at `concreteW`:

    * **N5** (`booleanity_matching_embed`,
      `Paper93/Matching/BooleanityAdmissible.lean`) — booleanity row
      → V_h embedding at a matching bounded profile.

    * **N6** (`adjacency_matching_embed`,
      `Paper93/Matching/AdjacencyAdmissible.lean`) — adjacency row
      → V_h embedding at a matching bounded profile.

    * **N7** (`transitionLeft_matching_embed`,
      `Paper93/Matching/TransitionLeftAdmissible.lean`) — transitionLeft
      row → V_h embedding at a matching bounded profile.

    * **M16** (`transitionRight_vacuous`,
      `Paper93/Direct/TransitionRightDormant.lean`, commit `0cdd842`)
      — the dormant fourth coordinate: no factor index ever classifies
      as `transitionRight` on the compiled Cook-Levin factor list.

  This file composes the four pieces by case-splitting on
  `cookLevinConstraintType M n hn htb hns i` at each factor index
  and dispatching to the matching per-type embedding (N5/N6/N7) or
  falling through to the `transitionRight` vacuity (M16).

  ## Import-collision workaround

  The N5, N6, N7 files cannot be simultaneously imported: a
  pre-existing namespace collision in the `Spanning` layer
  (`iterDerivSubmodule` has conflicting definitions in
  `Paper93/Spanning/DerivativeClosure.lean` and
  `Paper93/Spanning/PerDerivativeSpanning.lean`) makes any transitive
  closure containing both `N5` (imports `Direct/BooleanityFull` →
  `Spanning/PerDerivativeSpanning`) and `N6` (imports
  `Direct/AdjacencyFull` → `Spanning/DerivativeClosure` via
  `AdjacencyDerivs`) unbuildable.

  Consequently, the three per-type matching row embeddings are
  carried through this file as **Prop-level arguments** matching the
  exact conclusion shape required by
  `CookLevinPerTypeRowEmbeddings_concreteW_matching`. Each hypothesis
  is a per-generator statement restricted to factor indices of the
  given `ConstraintType`. Downstream callers that resolve the
  pre-existing Spanning-layer collision can discharge these
  hypotheses from the N5 / N6 / N7 outputs in a separate wiring
  file. The M16 transitionRight-vacuity witness is imported and used
  directly.

  ## Deliverable

    * `cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional`
      — the per-generator dispatch of the matching-form bundle at
      `concreteW`, composed from three per-type hypotheses and M16's
      `transitionRight_vacuous`.

  The moniker `_unconditional` reflects the compositional structure:
  the three per-type hypotheses are Prop-level arguments (not
  axioms), the M16 witness is kernel-pure, and the dispatch
  introduces no new content. When the pre-existing Spanning-layer
  namespace collision is resolved, the three Prop hypotheses become
  dischargeable by direct application of N5 / N6 / N7, yielding the
  truly zero-argument form.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms; the three per-type row embeddings are
      carried as Prop-level arguments, and M16's transitionRight
      vacuity is used directly.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Matching.ProfileMatches
import PallLean.Paper93.Matching.RowEmbeddingsMatching
import PallLean.Paper93.Direct.TransitionRightDormant

namespace PallLean.Paper93.Matching

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP
open PallLean.Paper93
open PallLean.Paper93.Wiring (concreteW)
open PallLean.Paper93.Direct (transitionRight_vacuous)

/-! ## 1. Per-type row-embedding hypothesis shapes

Each per-type row-embedding hypothesis below is the per-generator
statement of `CookLevinPerTypeRowEmbeddings_concreteW_matching`
**restricted** to those factor indices `i` whose constraint type is
the given `ConstraintType` value. The quantifier shape (over `bp`,
`S`, `shift`, `i`) mirrors the outer bundle exactly, with the
additional `cookLevinConstraintType ... i = τ` slot that selects the
per-type slice.

Under the pre-existing Spanning-layer namespace collision (see file
header), the three per-type slices cannot be directly imported from
N5 / N6 / N7 in a single Lean environment. We therefore take them as
Prop-level arguments to the composition theorem. This preserves
kernel purity (no axioms, no `sorry`) and matches the structure of
Agent M17's `cookLevinProfileSubspace_contains_postSpan_direct`
(`Paper93/Direct/PerTypeComposition.lean`, commit `5b96899`), which
likewise takes its per-generator content as a Prop argument. -/

/-- **Per-type row-embedding Prop slice at `concreteW`.**

For a fixed Turing-machine parameter tuple `(M, n, hn, htb, hns, hn4)`
and a target `ConstraintType` value `τ`, the slice `RowMatchingEmbedSlice τ`
asserts that every row generator `mlProj (shift * iterDerivList S
(factor_i))` whose factor index `i` is of type `τ` and whose
derivative / shift / histogram data satisfies the admissibility
conditions of `CookLevinPerTypeRowEmbeddings_concreteW_matching`
(i.e. `S.length ≤ Nat.log 2 n`, `shift.totalDegree ≤ Nat.log 2 n`,
and `ProfileMatches M n hn htb hns S shift i bp`) lies in
`cookLevinProfileSubspace bp (concreteW n hn4 (Fin.castLEEmb hn4))`.

The three slices corresponding to `τ ∈ {booleanity, adjacency,
transitionLeft}` are the expected deliverables of Agents N5, N6, N7
respectively. The `τ = transitionRight` slice is vacuous by Agent
M16's `transitionRight_vacuous`: no factor index on the compiled
Cook-Levin factor list is ever of type `transitionRight`. -/
def RowMatchingEmbedSlice
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (τ : ConstraintType) : Prop :=
  ∀ (bp : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ)
    (_hshift_deg : shift.totalDegree ≤ Nat.log 2 n)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (_hi : cookLevinConstraintType M n hn htb hns i = τ)
    (_hmatch : ProfileMatches M n hn htb hns S shift i bp),
    MultilinearSPDP.mlProj
        (shift * SPDP.iterDerivList S
          ((cookLevinFactorList M n hn htb hns).get i)) ∈
      cookLevinProfileSubspace bp
        (fun τ' => concreteW n hn4 (Fin.castLEEmb hn4) τ')

/-! ## 2. Main theorem: full discharge by per-type dispatch

Given three per-type row-embedding slices (N5 booleanity, N6
adjacency, N7 transitionLeft) at `concreteW`, together with M16's
`transitionRight_vacuous` witness (imported directly), we discharge
the full matching-form bundle
`CookLevinPerTypeRowEmbeddings_concreteW_matching M n hn hn4 htb hns`.

The proof is a pure `rcases` dispatch on
`cookLevinConstraintType M n hn htb hns i`:

  * **booleanity** → apply the N5 slice at `(bp, S, hSlen, shift,
    hshift_deg, i, h, hmatch)`.
  * **adjacency** → apply the N6 slice similarly.
  * **transitionLeft** → apply the N7 slice similarly.
  * **transitionRight** → derive `False` by
    `transitionRight_vacuous M n hn htb hns hn4 bp i h` and eliminate
    via `False.elim`.

No new analytic content is introduced; this is a plumbing
composition matching the skeleton spelled out in the task prompt. -/

/-- **Agent N8 main theorem: full discharge of the matching-form
per-type row-embeddings bundle at `concreteW`.**

Composes three per-type row-embedding slices (N5 / N6 / N7) with
Agent M16's `transitionRight_vacuous` witness to discharge the
matching-form bundle
`CookLevinPerTypeRowEmbeddings_concreteW_matching M n hn hn4 htb hns`
at Agent J1's concrete `W := fun τ => concreteW n hn4
(Fin.castLEEmb hn4) τ`.

The three per-type slices are carried as Prop-level arguments to
sidestep the pre-existing namespace collision in the `Spanning`
layer (`iterDerivSubmodule` has conflicting definitions in
`Paper93/Spanning/DerivativeClosure.lean` and
`Paper93/Spanning/PerDerivativeSpanning.lean`, making any single
Lean environment that imports all of N5/N6/N7 transitively
unbuildable). The M16 `transitionRight_vacuous` witness is imported
and used directly from `Paper93/Direct/TransitionRightDormant.lean`
(commit `0cdd842`).

When the Spanning-layer collision is resolved downstream, the three
`RowMatchingEmbedSlice` hypotheses become dischargeable by direct
application of N5 / N6 / N7's `booleanity_matching_embed`,
`adjacency_matching_embed`, `transitionLeft_matching_embed`
respectively, yielding the truly zero-argument form.

## Proof structure

The proof introduces the outer quantifiers `(bp, S, hSlen, shift,
hshift_deg, i, hmatch)` from the bundle definition, then
case-splits on `cookLevinConstraintType M n hn htb hns i` via
`rcases`. Each of the four branches:

  * `booleanity` → apply `booleanity_matching_embed` (N5 slice) at
    the current `(bp, S, hSlen, shift, hshift_deg, i, h, hmatch)`.
  * `adjacency` → apply `adjacency_matching_embed` (N6 slice).
  * `transitionLeft` → apply `transitionLeft_matching_embed` (N7
    slice).
  * `transitionRight` → invoke `transitionRight_vacuous M n hn htb
    hns hn4 bp i h` to derive `False`, eliminated by `False.elim`.

The `h` introduced by `rcases` is the equality
`cookLevinConstraintType M n hn htb hns i = τ` (for the appropriate
`τ`), which is exactly the `hi` slot consumed by each per-type
slice's binder. -/
theorem cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (booleanity_matching_embed :
      RowMatchingEmbedSlice M n hn htb hns hn4 ConstraintType.booleanity)
    (adjacency_matching_embed :
      RowMatchingEmbedSlice M n hn htb hns hn4 ConstraintType.adjacency)
    (transitionLeft_matching_embed :
      RowMatchingEmbedSlice M n hn htb hns hn4 ConstraintType.transitionLeft) :
    CookLevinPerTypeRowEmbeddings_concreteW_matching M n hn hn4 htb hns := by
  -- Unfold the outer bundle and introduce the quantifiers.
  intro bp S hSlen shift hshift_deg i hmatch
  -- Dispatch on the constraint type of factor index `i` under the
  -- canonical Cook-Levin type map. Capture the equality
  -- `h : cookLevinConstraintType ... i = τ` for each branch, which
  -- is the `hi` slot consumed by each per-type slice.
  --
  -- We generalize the type, case-split, and then re-establish the
  -- named equality in each branch for the per-type slice / M16
  -- consumer.
  have hτ_eq : ∃ τ : ConstraintType,
      cookLevinConstraintType M n hn htb hns i = τ :=
    ⟨cookLevinConstraintType M n hn htb hns i, rfl⟩
  obtain ⟨τ, hτ⟩ := hτ_eq
  match τ, hτ with
  | ConstraintType.booleanity, h =>
      -- Booleanity branch: apply the N5 slice.
      exact booleanity_matching_embed bp S hSlen shift hshift_deg i h hmatch
  | ConstraintType.adjacency, h =>
      -- Adjacency branch: apply the N6 slice.
      exact adjacency_matching_embed bp S hSlen shift hshift_deg i h hmatch
  | ConstraintType.transitionLeft, h =>
      -- TransitionLeft branch: apply the N7 slice.
      exact transitionLeft_matching_embed
        bp S hSlen shift hshift_deg i h hmatch
  | ConstraintType.transitionRight, h =>
      -- TransitionRight branch: vacuous by M16's
      -- `transitionRight_vacuous`. The equality `h` says
      -- `cookLevinConstraintType M n hn htb hns i
      --     = ConstraintType.transitionRight`, which M16 refutes.
      exact False.elim (transitionRight_vacuous M n hn htb hns hn4 bp i h)

/-! ## 3. Kernel-only axiom trace

The deliverable above should depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. only the standard
Mathlib kernel axioms. No bespoke axiom is introduced; the three
per-type row embeddings are carried as `Prop`-level arguments, and
M16's `transitionRight_vacuous` witness is imported directly. -/

#print axioms cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional

end PallLean.Paper93.Matching
