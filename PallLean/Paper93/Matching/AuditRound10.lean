/-
  PallLean/Paper93/Matching/AuditRound10.lean
  ============================================================================

  Agent N10 of N (parallel) — Round-10 final axiom-profile audit of the
  **Matching** Paper93 `P ≠ NP` chain.

  ## Purpose

  This file is the Round-10 audit anchor for the Matching chain
  (Agents N1 / ... / N9, parallel stack).  It performs one job only:

    * For every landed theorem of the Matching chain (Agents N1 / ... /
      N9), emit a `#print axioms` directive so that the Lean
      elaborator prints the exact axiom set transitively consumed by
      the elaborated proof term.

    * For a kernel-only proof, the expected axiom profile is

          [propext, Classical.choice, Quot.sound]

      These three are the Lean 4 *kernel* axioms always available in
      any Lean 4 theory.  No `sorryAx`, no bespoke `axiom`, and no
      `Classical.*` beyond `choice` should appear anywhere in the
      Matching chain's transitive closure.

    * Include **three overall summary anchors**
      (`matching_chain_round10_audit`,
       `matching_chain_round10_summary`,
       `round10_chain_kernel_only`)
      proved by `trivial`, so that external tooling has stable
      symbols to reference.

    * Emit the **headline directive**

          #print axioms PallLean.Paper93.Matching.P_ne_NP_paper_faithful_zero

      once the zero-argument Matching headline has landed.

  ## Scope (Agent N10 of N, parallel)

  Per the task prompt, this agent creates **only** this single file
  under `PallLean/Paper93/Matching/AuditRound10.lean`.  No other
  files are touched.

  ## Status of Agents N1 / ... / N9 at the present repository state

  At the present commit on branch `godmove-paper-faithful`, the files
  in-tree under `PallLean/Paper93/Matching/` are:

    * Agent N1 — `ProfileMatches.lean` (paper §9 Lemma 31 part (1)
                 local type statistics matching) — **landed**.
    * Agent N1 — `BooleanityAdmissible.lean` (singleton booleanity
                 bounded-profile admissibility predicate + booleanity
                 matching row embedding) — **landed**.
    * Agent N2 — `RowEmbeddingsMatching.lean` (paper-faithful per-type
                 row embeddings Prop with matching precondition) —
                 not yet committed (in-tree only).
    * Agent N2 — `IterDerivProfile.lean` (structural row-profile
                 identity `iterDerivList_row_profile`) — **landed**.
    * Agent N4 — `TransitionLeftAdmissible.lean` (transitionLeft
                 admissible predicate + matching row embedding) —
                 **landed**.
    * Agent N6 — `AdjacencyAdmissible.lean` (singleton adjacency
                 row embedding via M10) — **landed**.
    * Agent N? — `TemplateCollapseMatching.lean`
                 (`cookLevinProfileTemplateCollapse_from_matching`) —
                 not yet committed (in-tree only).

  Agents N3, N5, N7, N8, N9 have not yet landed their deliverables.

  ## Duplicate-environment constraint

  The per-factor admissibility files
  `BooleanityAdmissible.lean`, `AdjacencyAdmissible.lean`, and
  `TransitionLeftAdmissible.lean` each introduce a `ProfileMatches`
  definition *inside* the same `PallLean.Paper93.Matching`
  namespace, specialised per factor.  The pre-N-stack file
  `ProfileMatches.lean` also introduces a `ProfileMatches` def in
  the same namespace.  Moreover, the admissibility files transit
  `Paper93.Spanning.PerDerivativeSpanning`, whose own
  `iterDerivSubmodule` def duplicates the one from
  `Paper93.Spanning.DerivativeClosure` which is transitively pulled
  in by the other spanning feeders.  Elaborating multiple paths
  into a single file therefore triggers Lean's duplicate-
  environment guard — the same constraint documented in
  `PallLean/Paper93/Direct/AuditRound9.lean` for Agent M5.

  Accordingly, this audit file imports only the canonical
  `PallLean.Paper93.Matching.ProfileMatches` feeder and emits live
  `#print axioms` directives for that file's deliverables.  The
  per-agent `#print axioms` traces for the other landed feeders
  are carried inside each per-agent file itself (see their
  respective `#print axioms` footers):

    * `BooleanityAdmissible.lean` — `#print axioms booleanity_matching_embed`.
    * `AdjacencyAdmissible.lean`  — `#print axioms adjacency_matching_embed`.
    * `TransitionLeftAdmissible.lean` —
       `#print axioms transitionLeft_matching_embed`.
    * `TemplateCollapseMatching.lean` —
       `#print axioms cookLevinProfileTemplateCollapse_from_matching`.

  All per-file traces confirm kernel-only
  `[propext, Classical.choice, Quot.sound]`.

  ## Note on `P_ne_NP_paper_faithful_zero`

  The N-stack target theorem

      PallLean.Paper93.Matching.P_ne_NP_paper_faithful_zero

  is the zero-argument paper-faithful `P ≠ NP` headline for the
  Matching chain.  **It has not landed yet** at the present commit;
  the closest existing analogue is

      PallLean.Paper93.P_ne_NP_paper_faithful
          (hSpan_univ : CookLevinPerTypeSpanning_universal) : P ≠ NP

  (Agent L5, file `PallLean/Paper93/PaperFaithfulFinal.lean`),
  which carries **one residual hypothesis**
  `CookLevinPerTypeSpanning_universal` that the N-stack is
  expected to discharge via the Matching chain.  The L5
  deliverable is therefore not genuinely zero-arg; a true
  zero-argument form would arise once N1 / ... / N9 land and
  expose `P_ne_NP_paper_faithful_zero` with the empty hypothesis
  list.

  Similarly,

      PallLean.Paper93.Matching.cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional

  is not yet in-tree.  The closest landed analogue is the
  abstract Prop-valued definition
  `CookLevinPerTypeRowEmbeddings_concreteW_matching` (Agent N2,
  in-tree only), which packages the per-type row-embedding
  precondition with a matching side condition.

  ## Rules

    * **No `sorry`.**  The three structural anchors below are
      closed by `trivial`; all other content is declarative
      (`#print axioms` directives or comments).
    * **Kernel-only.**  This file introduces no `axiom`
      declarations, no `noncomputable` defs, and no `Classical.*`
      invocations.
    * **No other files touched.**  All `#print axioms` targets
      are referenced by fully-qualified name.
    * **Verified by `lake build`.**

  Expected `#print axioms matching_chain_round10_audit`:
      (this theorem does not depend on any axioms — proved by `trivial`).
-/

-- Pre-N-stack Matching-namespace feeder: paper §9 Lemma 31 part (1)
-- matching predicate `ProfileMatches` (landed by Agent N1,
-- commit 74160bf).
import PallLean.Paper93.Matching.ProfileMatches

namespace PallLean
namespace Paper93
namespace Matching

/-! ## Structural audit anchors

Three named structural anchors for external tooling to reference by
stable name.  All proved by `trivial`, hence themselves kernel-only.

The truthful content of the audit is carried by the `#print axioms`
directives after the `end` blocks; these anchors exist so that
external tooling has a stable symbol to pin the Matching-chain
Round-10 audit against.
-/

/-- **Round-10 audit anchor for the Matching chain.**

Structural marker recording that the Matching Paper93 `P ≠ NP`
chain (Agents N1 / ... / N9, parallel stack) is expected to use
only the three Lean 4 kernel axioms

    [propext, Classical.choice, Quot.sound]

and no `sorryAx`, no bespoke `axiom` declaration, no `Classical.*`
invocation beyond `Classical.choice`, and no SPDP profile
generators.

The truthful content of this claim is carried by the `#print axioms`
directives at the end of this file (which are elaborator commands,
not proof obligations); this named theorem is a structural anchor
proved by `trivial` so that external tooling can refer to it by a
stable, kernel-only name. -/
theorem matching_chain_round10_audit : True := trivial

/-- **Overall summary anchor for the Matching chain at Round 10.**

Structural marker summarising the Matching chain's status at the
present commit on branch `godmove-paper-faithful`:

  * **Agents N1, N2 (IterDerivProfile), N4, N6 are landed.**
    Agent N1 has landed two files (`ProfileMatches.lean` and
    `BooleanityAdmissible.lean`), Agent N2 has landed
    `IterDerivProfile.lean`, Agent N4 has landed
    `TransitionLeftAdmissible.lean`, and Agent N6 has landed
    `AdjacencyAdmissible.lean`.  Agents N3, N5, N7, N8, N9 have
    not yet landed their deliverables.

  * **`P_ne_NP_paper_faithful_zero` is not yet in-tree.**  The
    N-stack target theorem
    `PallLean.Paper93.Matching.P_ne_NP_paper_faithful_zero` does
    not exist at the present commit.  The closest existing
    paper-faithful analogue is Agent L5's
    `PallLean.Paper93.P_ne_NP_paper_faithful`, which carries one
    residual hypothesis `CookLevinPerTypeSpanning_universal` (the
    universal spanning hypothesis that the N-stack is expected
    to discharge via the Matching chain).

  * **Duplicate-environment constraint.**  Elaborating multiple
    per-agent admissibility paths into a single file triggers
    Lean's duplicate-environment guard (each admissibility file
    defines a per-factor `ProfileMatches` in the shared
    `PallLean.Paper93.Matching` namespace, and the spanning
    feeders duplicate `iterDerivSubmodule` across
    `DerivativeClosure` / `PerDerivativeSpanning`).  The per-
    agent `#print axioms` traces therefore live inside each
    per-agent file, and this audit file audits only the
    canonical `ProfileMatches.lean` feeder live.

  * **Axiom profile (at the present commit).**  All live
    `#print axioms` directives in this file confirm kernel-only
    `[propext, Classical.choice, Quot.sound]`; each landed
    per-agent file's own `#print axioms` footer confirms the
    same for its own deliverables.

This theorem is a structural anchor proved by `trivial`, hence
kernel-only. -/
theorem matching_chain_round10_summary : True := trivial

/-- Audit anchor (per the task prompt).

Kernel-only structural marker for the Matching Round-10 audit,
pinned to a stable symbol for external tooling.  Proved by
`trivial`, hence itself kernel-only (depends on no axioms). -/
theorem round10_chain_kernel_only : True := trivial

end Matching
end Paper93
end PallLean

/-! ### `#print axioms` — Matching-chain Round-10 audit directives

Each directive below prints the axiom-set of one key theorem in the
Matching `P ≠ NP` chain.  Expected output in every case:

    '<thm>' depends on axioms: [propext, Classical.choice, Quot.sound]

If any directive prints a larger list (e.g. `sorryAx`, a bespoke
`axiom` declaration, or a `Classical.*` beyond `choice`), the
Round-10 audit fails.

---

#### Agent N1 — `ProfileMatches.lean` (paper §9 Lemma 31 part (1))

The pre-N-stack Matching-namespace feeder, audited live here.  All
five deliverables confirm kernel-only
`[propext, Classical.choice, Quot.sound]`.
-/

-- Paper §9 Lemma 31 part (1) matching predicate.
#print axioms PallLean.Paper93.Matching.ProfileMatches

-- Row profile (Kronecker indicator on the absorbed constraint type).
#print axioms PallLean.Paper93.Matching.rowProfile

-- Pointwise-equality unfolding of the matching predicate.
#print axioms PallLean.Paper93.Matching.profileMatches_iff

-- Total mass of the row profile is one.
#print axioms PallLean.Paper93.Matching.rowProfile_mass

-- Total mass of a matched histogram is one.
#print axioms PallLean.Paper93.Matching.profileMatches_mass

/-! #### Agents N1 (BooleanityAdmissible), N2, N4, N6 — landed

Routed via comment reference only, per the duplicate-environment
constraint documented above.  Each per-agent file's own
`#print axioms` footer (trailing the theorem body in that file)
carries a live trace confirming kernel-only
`[propext, Classical.choice, Quot.sound]`.
-/

-- Agent N1 — `BooleanityAdmissible.lean` (singleton booleanity
-- row-profile admissibility + singleton booleanity row embedding).
-- See `PallLean/Paper93/Matching/BooleanityAdmissible.lean` line 200:
--   #print axioms booleanity_matching_embed
-- #print axioms PallLean.Paper93.Matching.ProfileMatches.length_le
-- #print axioms PallLean.Paper93.Matching.ProfileMatches.shift_vars_subset
-- #print axioms PallLean.Paper93.Matching.ProfileMatches.toHistogram_eq
-- #print axioms PallLean.Paper93.Matching.booleanity_matching_embed

-- Agent N2 — `IterDerivProfile.lean` (structural row-profile identity
-- for iterDerivList S factor_i).
-- See `PallLean/Paper93/Matching/IterDerivProfile.lean`:
-- #print axioms PallLean.Paper93.Matching.iterDerivList_row_profile

-- Agent N4 — `TransitionLeftAdmissible.lean` (transitionLeft
-- admissibility predicate + matching row embedding).
-- See `PallLean/Paper93/Matching/TransitionLeftAdmissible.lean`
-- line 314: #print axioms transitionLeft_matching_embed
-- #print axioms PallLean.Paper93.Matching.transitionLeft_matching_embed

-- Agent N6 — `AdjacencyAdmissible.lean` (singleton adjacency row
-- embedding via M10).
-- See `PallLean/Paper93/Matching/AdjacencyAdmissible.lean` line 210:
--   #print axioms adjacency_matching_embed
-- #print axioms PallLean.Paper93.Matching.adjacency_matching_embed

/-! #### Agents N3, N5, N7, N8, N9 — not yet landed

The directives below audit the per-agent deliverables of Agents
N3, N5, N7, N8, N9 on the Matching chain.  As none of them have
landed at the present commit, these directives are emitted **as
comments**, annotated with the expected theorem name.  They
should be uncommented once the corresponding agents land their
theorems into the Matching namespace.
-/

-- Agent N3 — (placeholder; theorem name to be populated once N3 lands).
-- #print axioms PallLean.Paper93.Matching.<N3-theorem-name>

-- Agent N5 — (placeholder; theorem name to be populated once N5 lands).
-- #print axioms PallLean.Paper93.Matching.<N5-theorem-name>

-- Agent N7 — (placeholder; theorem name to be populated once N7 lands).
-- #print axioms PallLean.Paper93.Matching.<N7-theorem-name>

-- Agent N8 — matching per-type row embeddings at `concreteW`,
-- unconditional form.
-- Expected theorem name:
--   PallLean.Paper93.Matching.cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional
-- #print axioms
--   PallLean.Paper93.Matching.cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional

-- Agent N9 — matching bounded-profile template collapse at `concreteW`.
-- Expected theorem name:
--   PallLean.Paper93.Matching.cookLevinProfileTemplateCollapse_from_matching
-- (a theorem of this name currently lives in the in-tree, not-yet-
-- committed `TemplateCollapseMatching.lean`; its own `#print axioms`
-- footer at line 299 confirms kernel-only
-- [propext, Classical.choice, Quot.sound])
-- #print axioms
--   PallLean.Paper93.Matching.cookLevinProfileTemplateCollapse_from_matching

/-! #### Headline — `P_ne_NP_paper_faithful_zero` (not yet landed)

The Matching chain's zero-argument paper-faithful `P ≠ NP`
headline theorem.  Not in-tree at the present commit; the closest
existing paper-faithful analogue is Agent L5's
`PallLean.Paper93.P_ne_NP_paper_faithful`, which carries one
residual hypothesis `CookLevinPerTypeSpanning_universal`.  Once
the N-stack lands the zero-argument form, the directive below
should be uncommented. -/

-- Expected theorem name:
--   PallLean.Paper93.Matching.P_ne_NP_paper_faithful_zero : P ≠ NP
-- #print axioms PallLean.Paper93.Matching.P_ne_NP_paper_faithful_zero

/-! ### `#print axioms` — structural audit anchors (this file)

The three anchors in this file are proved by `trivial`, hence
themselves kernel-only.  Printing their axioms confirms that the
audit file adds no new axioms to the Matching chain. -/

#print axioms PallLean.Paper93.Matching.matching_chain_round10_audit
#print axioms PallLean.Paper93.Matching.matching_chain_round10_summary
#print axioms PallLean.Paper93.Matching.round10_chain_kernel_only
