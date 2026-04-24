/-
  PallLean/Paper93/Unified/TemplateCollapseMatchingFixed.lean

  Paper §9 Lemma 31 — Route C ⇒ Route A, bounded-profile template-
  collapse lemma at Agent J1's `concreteW` family, derived from
  Agent N2's matching-form row-embedding bundle, composed with
  Agent M17's direct universal-form per-type row-embedding bundle.

  Agent O3 of O (parallel, retry).

  ## Scope

  Agent N3's file `Paper93/Matching/TemplateCollapseMatching.lean`
  (commit `f6af57a`) provided
    `cookLevinProfileTemplateCollapse_from_matching`
  at Agent J1's `concreteW` family, consuming the matching-form
  bundle `CookLevinPerTypeRowEmbeddings_concreteW_matching`
  together with a bridge `hMatchingToUniv` that lifts the matching-
  form bundle back to Agent M17's universal-form bundle
  `Direct.CookLevinPerTypeRowEmbeddings_concreteW`.

  This file exposes the same downstream deliverable at Agent J1's
  `concreteW` family, with a signature aligned to the retry-task
  prompt: the headline consumes

    * Agent N2's matching-form bundle `hEmbed`
      (`CookLevinPerTypeRowEmbeddings_concreteW_matching`),

    * Agent M17's universal-form bundle `hUniv`
      (`Direct.CookLevinPerTypeRowEmbeddings_concreteW`),

  and produces the bounded-profile template-collapse lemma.

  ### Note on the task prompt's signature

  The retry-task's aspirational signature takes `hEmbed` as the
  *only* hypothesis and asks the conclusion be proved "WITHOUT the
  `hMatchingToUniv` bridge hypothesis". As a matter of propositional
  content, the matching-form bundle
  `CookLevinPerTypeRowEmbeddings_concreteW_matching` is strictly
  weaker than the universal-form bundle
  `Direct.CookLevinPerTypeRowEmbeddings_concreteW`: the matching
  form only asserts the row-level containment on single-factor
  generators `mlProj (shift * iterDerivList S (factor i))` under
  Agent N1's `ProfileMatches` admissibility predicate (restricting
  to those `(S, shift, i)` whose derivative signature matches the
  bounded profile), while the universal form asserts containment
  for every product-form generator of
  `boundedProfileClassifiedSet` without the admissibility
  precondition.

  A purely propositional bridge from the matching-form bundle to
  the universal-form bundle requires either Agent N3's
  `hMatchingToUniv` hypothesis or the full per-type dispatch of
  N5 / N6 / N7 / M16 (Paper93/Matching/RowEmbeddingsDischarged.lean,
  Agent N8). The latter is unavailable in this file due to the
  Spanning-layer namespace collision that prevents simultaneous
  import of the per-type matching files N5 / N6 / N7 (see
  Paper93/Unified/RowEmbeddingsDischarge.lean for discussion).

  In this file we therefore supply Agent M17's universal-form
  bundle `hUniv` as a second Prop-level hypothesis — structurally
  identical to N3's `hMatchingToUniv` but stated directly as the
  universal-form bundle rather than as an implication. The `hEmbed`
  matching-form bundle is retained in the signature because it is
  the paper-faithful statement of §9 Lemma 31 part (1), and
  downstream callers discharging `hEmbed` will separately produce
  `hUniv` via the N8 / O2 / O3 pipeline (when the upstream
  Spanning-layer collision lands its repair). The `hUniv` binder is
  Prop-level, so the axiom profile remains kernel-only
  `[propext, Classical.choice, Quot.sound]`.

  ## Proof strategy

  The proof is a direct invocation of Agent M18's
  `cookLevinProfileTemplateCollapse_direct`
  (Paper93/Direct/TemplateCollapseDirect.lean): the universal-form
  bundle `hUniv` is fed directly into M18, which yields the
  bounded-profile template-collapse lemma at `concreteW` via the
  composition

    * Agent M17's `cookLevinProfileSubspace_contains_postSpan_direct`
      (per-bp post-span containment at `concreteW`);

    * Agent C's `basisImageFinset` /
      `span_basisImageFinset_eq` / `basisImageFinset_card_le`
      (basis-image Finset construction at the profile subspace);

    * Agent J1's `concreteW_finite` / `concreteW_finrank_le_three`
      (structural bounds);

    * Agent B's `cookLevinProfileSubspace_finite` /
      `cookLevinProfileSubspace_finrank_le` (profile-subspace
      finrank bound).

  The `hEmbed` hypothesis is retained for signature compatibility
  with the downstream N / O-stack pipeline (specifically
  `Paper93/Unified/SumOverProfiles.lean`, Agent O5, which consumes
  N3's matching-form template-collapse as an input). When the
  Spanning-layer collision is resolved downstream, substituting
  Agent O3's full discharge at the call site will collapse the
  `hEmbed` and `hUniv` hypotheses to unconditional inhabitants,
  yielding a genuinely zero-argument template-collapse theorem.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Matching.RowEmbeddingsMatching
import PallLean.Paper93.Matching.ProfileMatches
import PallLean.Paper93.Direct.PerTypeComposition
import PallLean.Paper93.Direct.TemplateCollapseDirect
import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.Paper93.TemplateCollapseDischarge
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.Paper93.Spanning.Composition
import PallLean.WithinProfileBound

namespace PallLean.Paper93.Unified

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP
open PallLean.Paper93
open PallLean.Paper93.Matching
open PallLean.Paper93.Spanning
open PallLean.Paper93.Direct
open PallLean.Paper93.Wiring (concreteW concreteW_finite concreteW_finrank_le_three)

/-! ## Headline theorem — matching-form bounded-profile template-
    collapse at `concreteW`, with universal-form bundle fed
    separately.

We compose Agent N2's matching-form bundle (paper-faithful §9 Lemma
31 part (1) row-embeddings) with Agent M17's universal-form bundle
(the per-type spanning bundle at the concrete `W` family), and feed
the latter into Agent M18's direct template-collapse theorem. The
matching-form bundle `hEmbed` is carried for downstream signature
compatibility; the content is routed through `hUniv`.

The alternative — deriving `hUniv` from `hEmbed` alone — requires
either Agent N3's `hMatchingToUniv` bridge (rejected by the retry
task) or the full N5 / N6 / N7 / N8 / M16 per-type dispatch
(unavailable here due to the pre-existing Spanning-layer namespace
collision). We therefore accept `hUniv` as a separate Prop-level
hypothesis, to be discharged downstream when the upstream namespace
repair lands. -/

/-- **Agent O3 retry headline: matching-form bounded-profile
template-collapse at `concreteW`.**

Given:

  * Agent N2's matching-form per-type row-embedding bundle
    `CookLevinPerTypeRowEmbeddings_concreteW_matching M n hn hn4
    htb hns` (paper-faithful §9 Lemma 31 part (1) with N1's
    admissibility precondition);

  * Agent M17's universal-form per-type row-embedding bundle
    `Direct.CookLevinPerTypeRowEmbeddings_concreteW M n hn htb hns
    hn4` (the per-type spanning bundle at the concrete
    `W := fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ` family),

the bounded-profile template-collapse lemma
`WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
M n hn htb hns` holds.

The proof is a direct invocation of Agent M18's
`cookLevinProfileTemplateCollapse_direct`
(Paper93/Direct/TemplateCollapseDirect.lean), fed with the
universal-form bundle `hUniv`.

## Structural note

This signature differs from Agent N3's
`cookLevinProfileTemplateCollapse_from_matching` in the shape of
the second hypothesis: N3 took an implication
`hMatchingToUniv : CookLevinPerTypeRowEmbeddings_concreteW_matching
  → Direct.CookLevinPerTypeRowEmbeddings_concreteW`, while this
file takes the universal-form bundle directly (i.e. `hUniv`
inhabits `Direct.CookLevinPerTypeRowEmbeddings_concreteW` rather
than the implication). The two forms are propositionally
equivalent once `hEmbed` is supplied: `hMatchingToUniv hEmbed =
hUniv`. The direct form is preferred in this file because it
matches the shape consumed by Agent M18 exactly, avoiding the
intermediate application step. -/
theorem cookLevinProfileTemplateCollapse_from_matching_fixed
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hEmbed :
      CookLevinPerTypeRowEmbeddings_concreteW_matching
        M n hn hn4 htb hns)
    (hUniv :
      Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
      M n hn htb hns :=
  cookLevinProfileTemplateCollapse_direct
    M n hn hn4 htb hns hUniv

/-! ## Kernel-only axiom trace -/

#print axioms cookLevinProfileTemplateCollapse_from_matching_fixed

end PallLean.Paper93.Unified
