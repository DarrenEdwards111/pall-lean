/-
  PallLean/Paper93/Alignment/G4Universal.lean

  Agent H9 (parallel, 9 of 10) — Alignment bridge between Agent G4's
  `cookLevinProfileSubspace_contains_postSpan_universal`
  (in `PallLean/Paper93/Spanning/Composition.lean`, taking a
  `CookLevinPerTypeSpanning_universal` hypothesis) and Agent G5's
  universal Prop `PallLean.Paper93.AgentG4_Spanning`
  (defined in `PallLean/Paper93/FinalDischarge.lean`).

  ## Scope

  This file does exactly one thing: it re-expresses G4's
  hypothesis-taking universal theorem as a direct inhabitant of
  `AgentG4_Spanning`, modulo the per-type spanning bundle
  `CookLevinPerTypeSpanning_universal` supplied by the per-type agents
  G1 (booleanity) / G2 (adjacency) / G3 (transitionLeft), eventually
  collated by H5.

  H5's `cookLevinPerTypeSpanning_discharged` has not yet landed in-repo.
  Per the task prompt's explicit fallback, we therefore keep the
  per-type bundle as an explicit hypothesis. When H5 lands, its
  conclusion will have exactly type `CookLevinPerTypeSpanning_universal`
  and can be plugged in directly at the use site.

  The shape of the produced theorem matches G5's `AgentG4_Spanning`
  Prop verbatim.

  ## Faithfulness

  The proof is a direct term-mode application of G4's
  `cookLevinProfileSubspace_contains_postSpan_universal`. No analytic
  content is added or simplified; we merely re-parenthesise the
  universal quantifiers and feed G5's binders into G4's conclusion.

  ## Axiom trace

  `#print axioms` at the end of this file should show only the
  kernel-level `propext`, `Classical.choice`, `Quot.sound` dependencies
  inherited from Mathlib, matching both G4 and G5.
-/

import PallLean.Paper93.Spanning.Composition
import PallLean.Paper93.FinalDischarge

open Module
open scoped BigOperators

namespace PallLean
namespace Paper93
namespace Alignment

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP
open PallLean.Paper93.Spanning

/-! ## Promotion of G4's universal theorem to G5's Prop

Agent G4 delivers

  `cookLevinProfileSubspace_contains_postSpan_universal :
      CookLevinPerTypeSpanning_universal →
        ∀ M n hn htb hns W, (∀ τ, Finite) → (∀ τ, finrank ≤ 3)
          → ∀ bp, cookLevinPostSpanAt ... ≤ cookLevinProfileSubspace bp W`

(see `PallLean/Paper93/Spanning/Composition.lean`). The right-hand
side of this implication is definitionally the body of Agent G5's
`AgentG4_Spanning` Prop (see `PallLean/Paper93/FinalDischarge.lean`).

We therefore expose, in a single theorem, the promotion

  `CookLevinPerTypeSpanning_universal → AgentG4_Spanning`

i.e. the alignment bridge that H5's discharge of the per-type spanning
bundle will plug into. When H5 lands its
`cookLevinPerTypeSpanning_discharged` inhabitant of
`CookLevinPerTypeSpanning_universal`, post-composing with `G4_universal`
yields a zero-argument proof of `AgentG4_Spanning` in-file.
-/

/-- **Alignment: G4 hypothesis-taking universal ⇒ G5's `AgentG4_Spanning`.**

    Given the per-type spanning bundle
    `CookLevinPerTypeSpanning_universal` (delivered by H5's composition
    of G1 / G2 / G3), promote G4's universal containment theorem into
    G5's universal Prop `PallLean.Paper93.AgentG4_Spanning`.

    The proof is a direct introduction of G5's binders followed by an
    application of G4's
    `cookLevinProfileSubspace_contains_postSpan_universal`. No new
    content is added; this is exclusively a shape-level alignment. -/
theorem G4_universal
    (hSpan : CookLevinPerTypeSpanning_universal) :
    PallLean.Paper93.AgentG4_Spanning := by
  intro M n hn htb hns W hW_fin hW_dim bp
  exact
    cookLevinProfileSubspace_contains_postSpan_universal
      hSpan M n hn htb hns W hW_fin hW_dim bp

/-! ## Alias

Alternative name matching the task spec's mnemonic — useful when
paired with H5's eventual `cookLevinPerTypeSpanning_discharged`
at the final composition site. -/

/-- Alias of `G4_universal` under the fully qualified name for
    clarity at the top-level `FinalDischarge` call site. -/
theorem agentG4_spanning_of_perTypeSpanning_universal
    (hSpan : CookLevinPerTypeSpanning_universal) :
    PallLean.Paper93.AgentG4_Spanning :=
  G4_universal hSpan

-- **Axiom audit** — expected: kernel-only
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms G4_universal
#print axioms agentG4_spanning_of_perTypeSpanning_universal

end Alignment
end Paper93
end PallLean
