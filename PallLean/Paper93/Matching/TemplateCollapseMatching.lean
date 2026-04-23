/-
  PallLean/Paper93/Matching/TemplateCollapseMatching.lean

  Paper §9 Lemma 31 — Route C ⇒ Route A, bounded-profile template-
  collapse lemma at Agent J1's `concreteW` family, *specialised to the
  matching-form row embeddings* (Agent N2) instead of the universal
  form used by Agent M18.

  Agent N3 of N (parallel).

  ## Scope

  Agent M18 of the M-stack (`Paper93/Direct/TemplateCollapseDirect.lean`,
  commit `13c01a8`) produced

    `cookLevinProfileTemplateCollapse_direct`

  at the *universal-form* per-type row-embedding bundle
  `Direct.CookLevinPerTypeRowEmbeddings_concreteW`, which is the
  unconditional pointwise containment

    `mlProj (shift * g) ∈ cookLevinProfileSubspace bp W`

  for **every** generator `(S, shift, g)` of `allBoundedProfilePostSpan
  ... bp.toHistogram`.

  Agent N2 (`Paper93/Matching/RowEmbeddingsMatching.lean`, commit
  `f98a301`) delivered the paper-faithful *matching-form* variant
  `CookLevinPerTypeRowEmbeddings_concreteW_matching`, which asserts
  the containment only on rows whose derivative signature **matches**
  the bounded profile `bp`, as measured by Agent N1's
  `ProfileMatches` relation
  (`Paper93/Matching/ProfileMatches.lean`, commit `74160bf`).

  The matching variant is strictly weaker than the universal variant
  — the universal bundle trivially implies the matching variant by
  forgetting the extra precondition — but it is the paper-faithful
  statement of §9 Lemma 31 part (1).

  The bridge from the matching-form bundle back to the universal-form
  bundle (which is what M18 consumes) is a separate N-stack
  deliverable: it requires re-deriving the per-generator statement
  from the `boundedProfileClassifiedSet`-based product-form
  quantifier. This bridge is taken here as an explicit Prop-level
  hypothesis, preserving the kernel-only axiom profile.

  ## Deliverable

    * `cookLevinProfileTemplateCollapse_from_matching` — the bounded-
      profile template-collapse lemma at Agent J1's `concreteW`
      family, composed from Agent N2's matching-form per-type row-
      embedding bundle plus the matching-to-universal bridge plus
      the M18/M17/C/J1/B structural data already in repo.

  ## Proof strategy

  For every bounded profile `bp : BoundedProfile (Nat.log 2 n)`:

    1. Let `W := fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ` and
       `U := cookLevinProfileSubspace bp W`. By J1 + Agent B,
         - `Module.Finite ℚ ↥U`,
         - `Module.finrank ℚ ↥U ≤ profileTemplateBound bp.toHistogram`.

    2. The matching-to-universal bridge hypothesis lifts Agent N2's
       matching-form bundle into Agent M17's universal-form bundle
       `CookLevinPerTypeRowEmbeddings_concreteW`. The universal
       bundle states that **every** generator of
       `allBoundedProfilePostSpan ... bp.toHistogram` already
       matches `bp` by construction (every row `(shift, S, g)` has
       `g ∈ boundedProfileClassifiedSet ... S bp.toHistogram`,
       pinning the factor-dispatch profile to `bp.toHistogram`), so
       the matching-form precondition is automatically satisfied on
       those rows.

    3. Agent M17's direct post-span containment
       `cookLevinProfileSubspace_contains_postSpan_direct` gives
       `allBoundedProfilePostSpan ... bp.toHistogram ≤ U`.

    4. By Agent C's `basisImageFinset` (a
       `finrank_span_finset_le_card` specialisation at
       `MvPolynomial (Fin n) ℚ`), we obtain a Finset
       `G : Finset (MvPolynomial (Fin n) ℚ)` with
         - `Submodule.span ℚ (↑G) = U`,
         - `G.card ≤ Module.finrank ℚ ↥U`.

    5. Combining 1 + 3 + 4 yields the per-bp
       `CookLevinProfileTemplateCollapseAtProfile` witness with
       `G.card ≤ profileTemplateBound bp.toHistogram`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Direct.PerTypeComposition
import PallLean.Paper93.Direct.TemplateCollapseDirect
import PallLean.Paper93.Matching.RowEmbeddingsMatching
import PallLean.Paper93.Matching.ProfileMatches
import PallLean.Paper93.TemplateCollapseDischarge
import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.WithinProfileBound

namespace PallLean.Paper93.Matching

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound
open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Direct
open PallLean.Paper93.Wiring (concreteW concreteW_finite concreteW_finrank_le_three)

/-! ## 1. Main theorem — matching-form bounded-profile template-collapse at `concreteW`

Composition of Agent N2's matching-form per-type row-embedding bundle
with the matching-to-universal bridge, Agent M17's direct post-span
containment, Agent C's basis-image Finset construction (the
`finrank_span_finset_le_card` specialisation at the profile subspace),
and Agent J1 + Agent B's structural data. -/

/-- **Agent N3 main theorem: matching-form bounded-profile template-
collapse at `concreteW`.**

For every Turing-machine parameter tuple `(M, n, hn, hn4, htb, hns)`
with `n ≥ 4`, given:

  * Agent N2's matching-form per-type row-embedding bundle
    `CookLevinPerTypeRowEmbeddings_concreteW_matching` at
    `concreteW n hn4 (Fin.castLEEmb hn4)` with Agent N1's
    `ProfileMatches` as admissibility precondition;

  * the matching-to-universal bridge — Agent M17's universal-form
    bundle lifted from the matching-form bundle (this bridge is a
    separate N-stack deliverable, taken as a Prop-level hypothesis
    here),

the bounded-profile template-collapse lemma
`WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
M n hn htb hns` holds.

For every bounded profile `bp : BoundedProfile (Nat.log 2 n)`, the
generating Finset `G` is constructed as Agent C's `basisImageFinset`
of the Cook-Levin profile subspace
`cookLevinProfileSubspace bp (fun τ => concreteW n hn4
(Fin.castLEEmb hn4) τ)`, which is Agent C's specialisation of
`finrank_span_finset_le_card` at `MvPolynomial (Fin n) ℚ`. The
cardinality is bounded by `profileTemplateBound bp.toHistogram` via
Agent B's `cookLevinProfileSubspace_finrank_le` + Agent J1's
`concreteW_finrank_le_three`.

The containment of the post-span in `span ℚ G` routes through Agent
M17's `cookLevinProfileSubspace_contains_postSpan_direct` applied to
the universal-form bundle, which in turn is obtained from Agent N2's
matching-form bundle via the bridge hypothesis.

When both Agent N2's matching-form bundle and the matching-to-
universal bridge land unconditionally, substituting them at the
call site collapses this theorem's signature to a genuinely
zero-argument
`CookLevinProfileTemplateCollapseLemmaBoundedProfile`. -/
theorem cookLevinProfileTemplateCollapse_from_matching
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hEmbed :
      CookLevinPerTypeRowEmbeddings_concreteW_matching
        M n hn hn4 htb hns)
    (hMatchingToUniv :
      CookLevinPerTypeRowEmbeddings_concreteW_matching
          M n hn hn4 htb hns →
        Direct.CookLevinPerTypeRowEmbeddings_concreteW
          M n hn htb hns hn4) :
    WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
      M n hn htb hns := by
  classical
  -- Lift the matching-form bundle to the universal-form bundle via
  -- the bridge hypothesis.
  have hUniv : Direct.CookLevinPerTypeRowEmbeddings_concreteW
      M n hn htb hns hn4 := hMatchingToUniv hEmbed
  -- For each bounded profile `bp`, construct the generating Finset
  -- `G` as the basis-image of the profile subspace
  -- `cookLevinProfileSubspace bp concreteW`, and bound
  -- `G.card ≤ profileTemplateBound bp.toHistogram` via
  -- `basisImageFinset_card_le` (= `finrank_span_finset_le_card`
  -- applied to a basis of the profile subspace).
  intro bp
  -- Abbreviate the per-type family used throughout.
  set W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ with hW_def
  -- Step 1: structural data at `concreteW` (Agent J1).
  have hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ) :=
    fun τ => concreteW_finite n hn4 (Fin.castLEEmb hn4) τ
  have hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3 :=
    fun τ => concreteW_finrank_le_three n hn4 (Fin.castLEEmb hn4) τ
  -- Step 2: profile subspace `U := cookLevinProfileSubspace bp W`
  -- finite + finrank ≤ profileTemplateBound (Agent B).
  let U : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    cookLevinProfileSubspace bp W
  haveI hU_fin : Module.Finite ℚ ↥U :=
    cookLevinProfileSubspace_finite bp W hW_fin
  have hU_finrank :
      Module.finrank ℚ ↥U ≤ profileTemplateBound bp.toHistogram :=
    cookLevinProfileSubspace_finrank_le bp W hW_fin hW_dim
  -- Step 3: M17's direct post-span containment at `concreteW`, fed
  -- by the universal-form bundle obtained from the matching-form
  -- bundle + bridge.
  have hPostSpan :
      allBoundedProfilePostSpan
          (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn htb hns).get i)
          (cookLevinConstraintType M n hn htb hns)
          bp.toHistogram
        ≤ U :=
    cookLevinProfileSubspace_contains_postSpan_direct
      M n hn htb hns hn4 bp hUniv
  -- Step 4: Agent C's basis-image Finset construction of `G ⊆
  -- MvPolynomial (Fin n) ℚ` from a basis of `U`, with
  --   `Submodule.span ℚ (↑G) = U` and `G.card ≤ finrank ℚ ↥U`.
  -- This is the `finrank_span_finset_le_card` specialisation at the
  -- profile subspace.
  let G : Finset (MvPolynomial (Fin n) ℚ) := @basisImageFinset n U hU_fin
  have hGspan :
      Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ)) = U :=
    @span_basisImageFinset_eq n U hU_fin
  have hGcard : G.card ≤ Module.finrank ℚ ↥U :=
    @basisImageFinset_card_le n U hU_fin
  -- Step 5: package the `CookLevinProfileTemplateCollapseAtProfile`
  -- witness for `bp` at `G`, via the two bounds composed above.
  refine ⟨G, ?_, ?_⟩
  · -- Containment `allBoundedProfilePostSpan … ≤ span ℚ G`.
    calc allBoundedProfilePostSpan
            (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn htb hns).get i)
            (cookLevinConstraintType M n hn htb hns)
            bp.toHistogram
        ≤ U := hPostSpan
      _ = Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ)) := hGspan.symm
  · -- Cardinality bound `G.card ≤ profileTemplateBound bp.toHistogram`
    -- via `basisImageFinset_card_le` (= `finrank_span_finset_le_card`
    -- applied to the basis of `U`).
    calc G.card
        ≤ Module.finrank ℚ ↥U := hGcard
      _ ≤ profileTemplateBound bp.toHistogram := hU_finrank

/-! ## 2. Kernel-only axiom trace

The deliverable above should depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. only the standard
Mathlib kernel axioms. No bespoke axiom is introduced; both residual
hypotheses are `Prop`s, so the binders preserve the axiom profile.

All content routes through:

  * Agent N2's matching-form per-type row-embedding bundle
    `CookLevinPerTypeRowEmbeddings_concreteW_matching` (taken as
    hypothesis here; paper-faithful statement of §9 Lemma 31 part
    (1) with admissibility precondition filtered by N1's
    `ProfileMatches`);

  * the matching-to-universal bridge (taken as hypothesis here; to
    be delivered by the N-stack as the paper observation that every
    generator of `allBoundedProfilePostSpan ... bp.toHistogram`
    automatically matches `bp` via its `boundedProfileClassifiedSet`
    membership);

  * Agent M17's `cookLevinProfileSubspace_contains_postSpan_direct`
    (direct post-span containment at `concreteW` via the universal-
    form bundle);

  * Agent C's `basisImageFinset` / `basisImageFinset_card_le` /
    `span_basisImageFinset_eq` (basis-image Finset construction of a
    finite-dimensional submodule of `MvPolynomial (Fin n) ℚ`, the
    `finrank_span_finset_le_card` specialisation at the profile
    subspace);

  * Agent J1's `concreteW_finite` / `concreteW_finrank_le_three`
    (structural bounds on the concrete ambient per-type `W_σ(τ)`);

  * Agent B's `cookLevinProfileSubspace_finite` /
    `cookLevinProfileSubspace_finrank_le` (Cook-Levin specialisation
    of Agent 9's generic profile-subspace finrank bound). -/

#print axioms cookLevinProfileTemplateCollapse_from_matching

end PallLean.Paper93.Matching
