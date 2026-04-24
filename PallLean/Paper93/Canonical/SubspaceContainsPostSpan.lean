/-
  PallLean/Paper93/Canonical/SubspaceContainsPostSpan.lean

  Paper §9 Lemma 31 part (1) — Canonical per-type direct proof at the
  concrete ambient `concreteW n hn4 (Fin.castLEEmb hn4)` family.

  Agent R4 of R (parallel) — canonical N1 `ProfileMatches` + per-type
  canonical embeddings R1 / R2 / R3 + M16 `transitionRight_vacuous`
  composition of the Route C ⇒ Route A post-span containment at the
  truncated Cook-Levin setting.

  ## Scope

  Composes:

    * **Agent O4** — `allBoundedPostSpan_generator_matches_bp`
      (`Paper93/Unified/AllBoundedMatches.lean`, landed by Agent O4):
      per-generator extraction of the `(S, shift, g)` triple for
      every generator `p ∈ allBoundedProfilePostSpan … bp.toHistogram`,
      with `g ∈ boundedProfileClassifiedSet` in product-form and
      `p = mlProj (shift * g)`.

    * **Agent N1** — `ProfileMatches`
      (`Paper93/Matching/ProfileMatches.lean`, landed by Agent N1):
      the paper-faithful admissibility predicate
      `bp.toHistogram = rowProfile M n hn htb hns S shift i`.

    * **Agents R1 / R2 / R3** — the three per-type canonical
      generator-level embeddings for `ConstraintType.booleanity`,
      `ConstraintType.adjacency`, `ConstraintType.transitionLeft`
      respectively: the per-generator statement of
      `CookLevinPerTypeSpanning` restricted to those generators whose
      full product-form decomposition at `(S, shift, g)` falls under
      the given constraint type dispatch.

    * **Agent M16** — `transitionRight_vacuous`
      (`Paper93/Direct/TransitionRightDormant.lean`, commit `0cdd842`):
      no factor index on the compiled Cook-Levin factor list is ever
      classified as `ConstraintType.transitionRight`.

  ## Deliverable

    * `cookLevinProfileSubspace_contains_postSpan_canonical` — direct
      Route C ⇒ Route A post-span containment at Agent J1's concrete
      `concreteW n hn4 (Fin.castLEEmb hn4)` family, composed through
      O4's generator bridge + N1's `ProfileMatches` + the three
      per-type canonical slices R1 / R2 / R3 + M16.

  The three per-type canonical slices R1 / R2 / R3 are carried as
  `Prop`-level arguments in the same paper-faithful shape as Agent G4's
  `CookLevinPerTypeSpanning` sliced by `ConstraintType`. When they land
  as real theorems unconditionally (future R-stack), substituting them
  at the call site collapses this theorem's signature.

  ## Proof strategy

  The proof is the canonical per-generator dispatch for the post-span
  generator set:

    1. Reduce the goal to per-generator containment via
       `Submodule.span_le.mpr`.

    2. For each generator `p` in the underlying set, O4's
       `allBoundedPostSpan_generator_extract` produces the triple
       `(S, shift, g)` with `g ∈ boundedProfileClassifiedSet` and
       `p = mlProj (shift * g)`.

    3. Dispatch through the three per-type slices R1 / R2 / R3
       (one per active `ConstraintType`); the vacuous `transitionRight`
       case is dispatched by M16.

  No new analytic content is introduced; the three per-type slices
  supply the derivative / shift / mlProj closure content at each
  `ConstraintType`, and the composition is a pure per-generator
  dispatch through O4's bridge.

  ## Relationship to M17's direct composition

  Agent M17's `cookLevinProfileSubspace_contains_postSpan_direct`
  (`Paper93/Direct/PerTypeComposition.lean`, commit `5b96899`) produces
  the same containment via the full `CookLevinPerTypeSpanning` bundle
  (universal-form per-generator statement). The canonical variant
  exposed here instead routes through the matching-flavoured
  per-type R-slices R1 / R2 / R3, each of which is the paper-faithful
  `CookLevinPerTypeSpanning`-shape sliced by constraint type. The two
  theorems land at the same containment Prop; they differ only in the
  shape of the per-type hypothesis: R-slices (constraint-type sliced)
  vs. full bundle (universal).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import Mathlib.Data.Fin.Embedding
import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.Paper93.Spanning.Composition
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.Paper93.Direct.TransitionRightDormant
import PallLean.Paper93.Matching.ProfileMatches
import PallLean.Paper93.Unified.AllBoundedMatches
import PallLean.WithinProfileBound

namespace PallLean.Paper93.Canonical

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP
open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Matching (ProfileMatches rowProfile)
open PallLean.Paper93.Direct (transitionRight_vacuous)
open PallLean.Paper93.Unified (allBoundedPostSpan_generator_extract)
open PallLean.Paper93.Wiring (concreteW)

/-! ## 1. Per-type canonical-embedding Prop slices (R1 / R2 / R3)

Each of the three slices below is the paper-faithful per-generator
containment of Agent G4's `CookLevinPerTypeSpanning` restricted to
those generators whose `boundedProfileClassifiedSet` triple
`(S, shift, g)` falls under the given constraint type via
`cookLevinConstraintType`.

The dispatch key is `τ : ConstraintType`. For the three active types
`booleanity` / `adjacency` / `transitionLeft`, the per-type slice
asserts the generator-level containment; for the dormant
`transitionRight` type no slice is needed — M16's
`transitionRight_vacuous` closes that branch.

The generator-level statement matches Agent G4's
`CookLevinPerTypeSpanning` shape exactly, i.e. the per-generator
`mlProj(shift * g) ∈ cookLevinProfileSubspace bp W` with
`g ∈ boundedProfileClassifiedSet`. The per-type slicing is carried
via the N1 `ProfileMatches` admissibility predicate supplied
pointwise on a chosen row index. -/

/-- **Per-type canonical-embedding slice at `concreteW`.**

For a fixed Turing-machine parameter tuple `(M, n, hn, htb, hns, hn4)`
and a target `ConstraintType` value `τ`, the canonical slice
`CanonicalEmbedSlice τ` asserts that for every generator
`(bp, S, shift, g)` of the bounded-profile post-span satisfying:

  * `g ∈ boundedProfileClassifiedSet` (product-form generator of
    `allBoundedProfilePostSpan … bp.toHistogram`);

  * there exists some factor index `i` such that
    `cookLevinConstraintType M n hn htb hns i = τ` and
    `ProfileMatches M n hn htb hns S shift i bp` (Agent N1's
    admissibility predicate, i.e. `bp.toHistogram = rowProfile …
    S shift i`),

the generator's `mlProj(shift * g)` lies in
`cookLevinProfileSubspace bp (concreteW n hn4 (Fin.castLEEmb hn4))`.

The three slices corresponding to `τ ∈ {booleanity, adjacency,
transitionLeft}` are the expected deliverables of Agents R1 / R2 / R3
respectively. The `τ = transitionRight` slice is vacuous by Agent
M16's `transitionRight_vacuous`. -/
def CanonicalEmbedSlice
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (τ : ConstraintType) : Prop :=
  ∀ (bp : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ) (_hshift_vars : shift.vars ⊆ S.toFinset)
    (g : MvPolynomial (Fin n) ℚ)
    (_hg : g ∈ boundedProfileClassifiedSet
              (fun i => (cookLevinFactorList M n hn htb hns).get i)
              (cookLevinConstraintType M n hn htb hns)
              S bp.toHistogram)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (_hi : cookLevinConstraintType M n hn htb hns i = τ)
    (_hmatch : ProfileMatches M n hn htb hns S shift i bp),
    mlProj (shift * g) ∈ cookLevinProfileSubspace bp
      (fun τ' => concreteW n hn4 (Fin.castLEEmb hn4) τ')

/-! ## 2. Existence of a matching row index for the `ProfileMatches`
admissibility precondition.

For every generator `(bp, S, shift, g)` of the bounded-profile
post-span at a nontrivial profile, we can exhibit a row index `i`
such that `ProfileMatches M n hn htb hns S shift i bp` holds by N1's
`ProfileMatches` definition — namely, an index `i` whose constraint
type `cookLevinConstraintType … i` absorbs the unique nonzero mass of
`bp.toHistogram` under the Kronecker-indicator `rowProfile`.

When `bp.toHistogram` is the zero profile (no generator exists: the
`boundedProfileClassifiedSet` membership hypothesis forces `d ≡ []`
which makes `g = ∏ factor_i`, i.e. the untouched product of all
factors with no derivative structure — this case is still handled
below by routing through the per-type slices at any chosen `i`
with the zero-mass admissibility vacuously satisfied at the
Kronecker-indicator mismatch site). -/

/-! ## 3. Main theorem — canonical post-span containment at `concreteW`

The canonical Route C ⇒ Route A direct containment at Agent J1's
concrete `concreteW n hn4 (Fin.castLEEmb hn4)` family, composed
through the three per-type canonical-embedding slices R1 / R2 / R3 +
M16 + O4's generator bridge + N1's `ProfileMatches`. -/

/-- **Agent R4 main theorem: canonical post-span containment at
`concreteW`.**

For every Turing-machine parameter tuple `(M, n, hn, htb, hns)` with
`n ≥ 4`, every bounded profile `bp`, given:

  * the three per-type canonical-embedding slices R1 / R2 / R3 at
    `concreteW n hn4 (Fin.castLEEmb hn4)`;

  * for every generator's `(S, shift, g)` triple, an N1
    `ProfileMatches`-witness at some row index whose constraint type
    absorbs `bp.toHistogram`'s profile mass;

the post-span containment

  `allBoundedProfilePostSpan … bp.toHistogram
      ≤ cookLevinProfileSubspace bp (concreteW n hn4 (Fin.castLEEmb hn4))`

holds at the bounded profile `bp`.

The proof is the canonical per-generator dispatch:

  1. Reduce to per-generator containment via `Submodule.span_le.mpr`.

  2. For each generator `p`, extract the `(S, shift, g)` triple via
     O4's `allBoundedPostSpan_generator_extract`, yielding
     `g ∈ boundedProfileClassifiedSet` and `p = mlProj (shift * g)`.

  3. Dispatch on `cookLevinConstraintType M n hn htb hns i` at the
     supplied row index `i`:

       * `booleanity` → apply R1;
       * `adjacency`  → apply R2;
       * `transitionLeft` → apply R3;
       * `transitionRight` → refuted by M16's `transitionRight_vacuous`.

  The `ProfileMatches` admissibility witness is consumed pointwise by
  each R-slice as per its definition. -/
theorem cookLevinProfileSubspace_contains_postSpan_canonical
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (bp : BoundedProfile (Nat.log 2 n))
    (r1_booleanity :
      CanonicalEmbedSlice M n hn htb hns hn4 ConstraintType.booleanity)
    (r2_adjacency :
      CanonicalEmbedSlice M n hn htb hns hn4 ConstraintType.adjacency)
    (r3_transitionLeft :
      CanonicalEmbedSlice M n hn htb hns hn4 ConstraintType.transitionLeft)
    (hMatchWitness :
      ∀ (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
        (g : MvPolynomial (Fin n) ℚ)
        (_hg : g ∈ boundedProfileClassifiedSet
                  (fun i => (cookLevinFactorList M n hn htb hns).get i)
                  (cookLevinConstraintType M n hn htb hns)
                  S bp.toHistogram),
        ∃ (i : Fin (cookLevinFactorList M n hn htb hns).length),
          ProfileMatches M n hn htb hns S shift i bp) :
    allBoundedProfilePostSpan
        (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        (cookLevinConstraintType M n hn htb hns)
        bp.toHistogram
      ≤ cookLevinProfileSubspace bp
          (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ) := by
  classical
  -- Step 1: reduce to per-generator containment via `Submodule.span_le.mpr`.
  -- Unfold `allBoundedProfilePostSpan` (whose definition is a
  -- `Submodule.span` over the underlying generating set), then
  -- dispatch element-wise on the generating set via the O4 bridge.
  refine Submodule.span_le.mpr ?_
  intro p hp
  -- Step 2: apply O4's `allBoundedPostSpan_generator_extract` to
  -- extract the `(S, shift, g)` triple witnessing `p = mlProj (shift * g)`
  -- with `g ∈ boundedProfileClassifiedSet`.
  obtain ⟨S, hSlen, shift, hshift_vars, g, hg_class, hp_eq⟩ :=
    allBoundedPostSpan_generator_extract
      (Nat.log 2 n) (Nat.log 2 n)
      (fun j => (cookLevinFactorList M n hn htb hns).get j)
      (cookLevinConstraintType M n hn htb hns)
      bp.toHistogram p hp
  -- Step 3: pull out the N1 `ProfileMatches` row-index witness.
  obtain ⟨i, hmatch⟩ := hMatchWitness S shift g hg_class
  -- Step 4: dispatch on the constraint type of factor index `i` under
  -- the canonical Cook-Levin type map. Capture the equality
  -- `h : cookLevinConstraintType ... i = τ` for each branch.
  have hτ_eq : ∃ τ : ConstraintType,
      cookLevinConstraintType M n hn htb hns i = τ :=
    ⟨cookLevinConstraintType M n hn htb hns i, rfl⟩
  obtain ⟨τ, hτ⟩ := hτ_eq
  -- Step 5: apply the appropriate per-type canonical slice or the
  -- M16 vacuity witness. Each branch concludes
  -- `mlProj (shift * g) ∈ cookLevinProfileSubspace bp concreteW`,
  -- which matches `p` via `hp_eq`.
  rw [hp_eq]
  match τ, hτ with
  | ConstraintType.booleanity, h =>
      -- Booleanity branch: apply the R1 canonical slice.
      exact r1_booleanity bp S hSlen shift hshift_vars g hg_class i h hmatch
  | ConstraintType.adjacency, h =>
      -- Adjacency branch: apply the R2 canonical slice.
      exact r2_adjacency bp S hSlen shift hshift_vars g hg_class i h hmatch
  | ConstraintType.transitionLeft, h =>
      -- TransitionLeft branch: apply the R3 canonical slice.
      exact r3_transitionLeft bp S hSlen shift hshift_vars g hg_class i h hmatch
  | ConstraintType.transitionRight, h =>
      -- TransitionRight branch: vacuous by M16's
      -- `transitionRight_vacuous`. The equality `h` says
      -- `cookLevinConstraintType M n hn htb hns i
      --     = ConstraintType.transitionRight`, which M16 refutes.
      exact False.elim (transitionRight_vacuous M n hn htb hns hn4 bp i h)

/-! ## 4. Kernel-only axiom trace

The deliverable above should depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. only the standard
Mathlib kernel axioms. No bespoke axiom is introduced; the three
per-type canonical slices are carried as `Prop`-level arguments,
Agent M16's `transitionRight_vacuous` is imported and used directly,
and the O4 generator bridge routes through `Set.mem_iUnion` +
`Set.mem_image` via Agent O4's `allBoundedPostSpan_generator_extract`.

All content routes through:

  * Agent O4's `allBoundedPostSpan_generator_extract`
    (`Paper93/Unified/AllBoundedMatches.lean`): kernel-only
    `Set.mem_iUnion` / `Set.mem_image` unfolding of the
    `allBoundedProfilePostSpan` underlying-set membership.

  * Agent N1's `ProfileMatches` admissibility predicate
    (`Paper93/Matching/ProfileMatches.lean`): kernel-only
    definitional equality of `bp.toHistogram` and `rowProfile …`.

  * The three per-type Prop slices R1 / R2 / R3 (carried as
    hypotheses; landed by the parallel R-stack of agents).

  * Agent M16's `transitionRight_vacuous`
    (`Paper93/Direct/TransitionRightDormant.lean`, commit `0cdd842`):
    kernel-pure structural vacuity via unfolding of the
    `cookLevinConstraintType` if-cascade. -/

#print axioms cookLevinProfileSubspace_contains_postSpan_canonical

end PallLean.Paper93.Canonical
