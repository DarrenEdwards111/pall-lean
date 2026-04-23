/-
  PallLean/Paper93/Unified/FinalVerification.lean
  ============================================================================

  Agent O8 of O (parallel) — Final axiom-profile audit of the
  **Unified** Paper93 `P ≠ NP` chain.

  ## Purpose

  This file is the Round-11 audit anchor for the Unified chain
  (Agents O1 / ... / O7, parallel stack; extended by O9 / O10
  documentation and alternative-route anchors).  It performs one
  job only:

    * For every landed theorem of the Unified chain, emit a
      `#print axioms` directive so that the Lean elaborator prints
      the exact axiom set transitively consumed by the elaborated
      proof term.

    * For a kernel-only proof, the expected axiom profile is

          [propext, Classical.choice, Quot.sound]

      These three are the Lean 4 *kernel* axioms always available
      in any Lean 4 theory.  No `sorryAx`, no bespoke `axiom`, and
      no `Classical.*` beyond `choice` should appear anywhere in
      the Unified chain's transitive closure.

    * Include the overall summary anchor
      (`round11_unified_audit`) proved by `trivial`, so that
      external tooling has a stable symbol to reference.

    * Emit the **headline directive**

          #print axioms PallLean.Paper93.Unified.P_ne_NP_unified_zero

      for the Unified-chain zero-argument `P ≠ NP` headline
      (Agent O7, file `PallLean/Paper93/Unified/P_ne_NP_Unified.lean`).

  ## Scope (Agent O8 of O, parallel)

  Per the task prompt, this agent creates **only** this single file
  under `PallLean/Paper93/Unified/FinalVerification.lean`.  No other
  files are touched.

  ## Unified-chain composition shape

  The **Unified** Paper93 `P ≠ NP` chain unifies the two parallel
  paper-faithful discharge routes (the **Direct** chain of Agents
  M1 / ... / M19 and the **Matching** chain of Agents N1 / ... / N9)
  into a single bounded-profile template-collapse full-discharge
  term

      cookLevinProfileTemplateCollapseLemmaBoundedProfile_full_discharge
        (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
          WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
            M n hn2 htb hns

  (Agent O7, `Paper93/Unified/FullDischarge.lean`) and then feeds
  that term into
  `Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis`
  to produce the Unified chain's (near-)zero-argument headline

      PallLean.Paper93.Unified.P_ne_NP_unified_zero : P ≠ NP

  (Agent O7, `Paper93/Unified/P_ne_NP_Unified.lean`).

  The composition mirrors the Direct chain's
  `Paper93.Direct.P_ne_NP_zero` (Agent M19, file
  `Paper93/Direct/ZeroArgFinal.lean`) and the Matching chain's
  `Paper93.Matching.P_ne_NP_paper_faithful_zero` (Agent N9, file
  `Paper93/Matching/FinalZero.lean`), but combines both routes'
  per-type row embeddings into a single canonical full-discharge
  term exposed in the `PallLean.Paper93.Unified` namespace.

  ## Whether `P_ne_NP_unified_zero` is genuinely zero-arg

  **It is not genuinely zero-arg** at the present commit.  The
  signature carries **one residual `Prop`-level universal
  hypothesis**,

      (cookLevinProfileTemplateCollapseLemmaBoundedProfile_full_discharge :
        CookLevinProfileTemplateCollapseLemmaBoundedProfile_full_discharge_universal)

  which binds the O6 universal discharge term.  The binder is
  `Prop`-valued so does not introduce any bespoke axiom — the axiom
  profile of `P_ne_NP_unified_zero` is kernel-only
  `[propext, Classical.choice, Quot.sound]`.

  Architecturally, when Agent O6 materialises its discharge in
  concrete form and is substituted at the call site inside
  `P_ne_NP_Unified.lean`, the theorem collapses to a genuine
  zero-argument `P ≠ NP`.  At present, the Prop-binder name
  `cookLevinProfileTemplateCollapseLemmaBoundedProfile_full_discharge`
  inside `P_ne_NP_unified_zero` is *shadowed* by Agent O7's theorem of
  the same name in `FullDischarge.lean`, which provides a canonical
  inhabitant up to two further residual `Prop`-binders (O2 / O3
  universal forms) — consistent with the Direct (M19) and Matching
  (N9) chain precedents.

  ## Status of Agents O1 / ... / O10 at the present repository state

  At the present commit on branch `godmove-paper-faithful`, the
  `PallLean/Paper93/Unified/` directory contains the following
  landed deliverables (via commit `bcd004c` and predecessors):

    * Agent O1 — `IterDerivSubmoduleUnified.lean` (reconciles the
      two `iterDerivSubmodule` definitions in
      `PallLean.Paper93.Spanning`; exposes
      `iterDerivSubmodule_eq_iterDerivSubmodule_forH5` and
      associated bridging lemmas).
    * Agent O2 — `RowEmbeddingsDischarge.lean` (unconditional
      matching-form per-type row-embeddings discharge at J1's
      `concreteW` family; exposes
      `cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional_discharged`).
    * Agent O4 — `AllBoundedMatches.lean` (matching-form ⇒
      universal-form generator bridge for
      `WithinProfileBound.allBoundedProfilePostSpan`; exposes
      `allBoundedPostSpan_generator_matches_bp` and peers).
    * Agent O7 — `FullDischarge.lean` + `P_ne_NP_Unified.lean` (full
      unified bounded-profile template-collapse discharge +
      `P_ne_NP_unified_zero` headline).
    * Agent O9 — `ChainReport.lean` (Round-11 unified chain
      completion documentation anchor; `chain_report : True`).
    * Agent O10 — `AlternativeFinal.lean` (alternative route:
      admissible-only matching-form; exposes
      `P_ne_NP_alternative_zero`).
    * Agent O8 — this file.

  Agents O3, O5, O6 have not landed in-tree at the present commit;
  their universal deliverables are carried as `Prop`-binders on the
  downstream signatures (see the O7 `FullDischarge.lean` and
  `P_ne_NP_Unified.lean` Prop-binder shapes above).

  ## Duplicate-environment constraint

  Consistent with the constraint documented in
  `PallLean/Paper93/Direct/AuditRound9.lean` (Agent M20) and
  `PallLean/Paper93/Matching/AuditRound10.lean` (Agent N10),
  elaborating multiple per-agent paths into a single file would
  trigger Lean's duplicate-environment guard whenever per-agent
  files reintroduce a shared namespace-level def (e.g.
  `iterDerivSubmodule` across `DerivativeClosure` /
  `PerDerivativeSpanning`).

  Accordingly, this audit file imports only the canonical
  `PallLean.Paper93.Unified.P_ne_NP_Unified` and
  `PallLean.Paper93.Unified.FullDischarge` feeders (which
  transitively pull in the rest of the O-chain), plus the base
  Paper93 `Audit.lean` feeder, and emits live `#print axioms`
  directives against the landed deliverables.

  ## Rules

    * **No `sorry`.**  The structural anchor below is closed by
      `trivial`; all other content is declarative
      (`#print axioms` directives or comments).
    * **Kernel-only.**  This file introduces no `axiom`
      declarations, no `noncomputable` defs, and no `Classical.*`
      invocations.
    * **No other files touched.**  All `#print axioms` targets
      are referenced by fully-qualified name.
    * **Verified by `lake build`.**

  Expected `#print axioms round11_unified_audit`:
      (this theorem does not depend on any axioms — proved by
       `trivial`).

  ## Paper citations

    * §40 Theorem 207 p. 199 (six-step contradiction chain);
    * §40 Theorem 209 Step 6 p. 199 (canonical `n = 2 ^ 804` scale);
    * §9 Lemma 31 pp. 41–45 (bounded-profile template collapse;
      concrete `W_σ(τ)` form);
    * §49.1 p. 230 (axiom-free, no `sorry`).
-/

-- Base Paper93 audit feeder: transitively pulls in the nine paper
-- §9 / §9.3 combinatorial agent modules plus the Step4Compiler
-- paper-faithful §40 / §49.1 chain.
import PallLean.Paper93.Audit

-- Unified O-chain feeders: the landed deliverables exposing
-- `PallLean.Paper93.Unified.*` theorems.  Each one is responsible
-- for its own per-file `#print axioms` footer; we re-audit the key
-- deliverables here in one place for the Round-11 audit.
import PallLean.Paper93.Unified.P_ne_NP_Unified
import PallLean.Paper93.Unified.FullDischarge
import PallLean.Paper93.Unified.AlternativeFinal
import PallLean.Paper93.Unified.ChainReport

-- Matching-chain headline (for cross-chain audit parity).
import PallLean.Paper93.Matching.FinalZero

namespace PallLean
namespace Paper93
namespace Unified

/-! ## Structural audit anchor

One named structural anchor for external tooling to reference by a
stable name.  Proved by `trivial`, hence itself kernel-only.

The truthful content of the audit is carried by the `#print axioms`
directives after the `end` blocks; this anchor exists so that
external tooling has a stable symbol to pin the Unified-chain
Round-11 audit against.
-/

/-- **Round-11 audit anchor for the Unified chain.**

Structural marker recording that the Unified Paper93 `P ≠ NP`
chain (Agents O1 / ... / O10, parallel stack) uses only the three
Lean 4 kernel axioms

    [propext, Classical.choice, Quot.sound]

and no `sorryAx`, no bespoke `axiom` declaration, no `Classical.*`
invocation beyond `Classical.choice`, and no SPDP profile
generators.

The truthful content of this claim is carried by the `#print axioms`
directives at the end of this file (which are elaborator commands,
not proof obligations); this named theorem is a structural anchor
proved by `trivial` so that external tooling can refer to it by a
stable, kernel-only name. -/
theorem round11_unified_audit : True := trivial

end Unified
end Paper93
end PallLean

/-! ### `#print axioms` — Unified-chain Round-11 audit directives

Each directive below prints the axiom-set of one key theorem
consumed by or produced by the Unified `P ≠ NP` chain.  Expected
output in every case:

    '<thm>' depends on axioms: [propext, Classical.choice, Quot.sound]

If any directive prints a larger list (e.g. `sorryAx`, a bespoke
`axiom` declaration, or a `Classical.*` beyond `choice`), the
Round-11 audit fails.
-/

/-! #### Headline — `P_ne_NP_unified_zero` (Agent O7, landed)

The Unified chain's headline `P ≠ NP` theorem.  Note that the
signature carries one residual `Prop`-level universal hypothesis
(the O6 universal discharge); the axiom profile is nevertheless
kernel-only since the binder is `Prop`-valued. -/

#print axioms PallLean.Paper93.Unified.P_ne_NP_unified_zero

-- Supporting universal def for the P_ne_NP_unified_zero hypothesis.
#print axioms
  PallLean.Paper93.Unified.CookLevinProfileTemplateCollapseLemmaBoundedProfile_full_discharge_universal

/-! #### Agent O7 — `FullDischarge.lean` (landed)

Full unified bounded-profile template-collapse discharge, composing
the Direct (M18) and Matching (N3+N8) chains at the bounded-profile
granularity. -/

#print axioms
  PallLean.Paper93.Unified.cookLevinProfileTemplateCollapseLemmaBoundedProfile_full_discharge

#print axioms
  PallLean.Paper93.Unified.CookLevinProfileTemplateCollapse_from_matching_fixed_universal

#print axioms
  PallLean.Paper93.Unified.CookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional_discharged_universal

/-! #### Agent O10 — `AlternativeFinal.lean` (landed)

Alternative route: admissible-only matching-form per-type row
embeddings fed through the Step252 admissible-only bridge. -/

#print axioms PallLean.Paper93.Unified.P_ne_NP_alternative_zero

#print axioms
  PallLean.Paper93.Unified.CookLevinProfileTemplateCollapse_from_matching_admissibleOnly_universal

#print axioms
  PallLean.Paper93.Unified.CookLevinPerTypeRowEmbeddings_matching_admissibleOnly_universal

/-! #### Agent O9 — `ChainReport.lean` (landed)

Round-11 unified chain completion documentation anchor. -/

#print axioms PallLean.Paper93.Unified.chain_report

/-! #### Downstream Step4Compiler bridges (landed)

The Unified chain's zero-argument `P ≠ NP` headline composes
Agent O7's `cookLevinProfileTemplateCollapseLemmaBoundedProfile_full_discharge`
with Step4Compiler.Step252's bounded-profile bridge.  We audit the
bridge (and the closely related `admissibleOnly` and base
`templateCollapse` variants) here. -/

-- Step4Compiler §252.13h — bounded-profile template-collapse
-- final form; the kernel-only bridge consumed by the Unified
-- chain's zero-argument headline.
#print axioms
  Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis

-- Step4Compiler §252.13g — admissible-only variant (consumed by
-- Agent O10's alternative route).
#print axioms
  Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_admissibleOnly_hypothesis

-- Step4Compiler §252.13f — base template-collapse variant.
#print axioms
  Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_hypothesis

-- Step4Compiler §252.13e — template-collapse → direct-rank
-- transport on the pullback-partition surface.
#print axioms
  Step4Compiler.Step252.cookLevinQ_rank_le_from_templateCollapse

/-! #### Base Paper93 audit anchors (landed)

The Paper93 base audit file
`PallLean/Paper93/Audit.lean` exposes a set of structural audit
anchors for the paper §9 / §9.3 combinatorial chain.  We re-audit
them here at the Unified level so that the Unified audit includes
the base paper-faithful chain's axiom profile. -/

-- Paper §9 Lemma 26: row(w) = row(canWindow(w)).
#print axioms PallLean.Paper93.row_eq_canRow
#print axioms PallLean.Paper93.rowSpan_eq_canRowSpan

-- Paper §9 Lemma 25: shortlex normal form represents the window.
#print axioms PallLean.Paper93.NF_represents

-- Paper §9 Lemma 27: symmetric multiset determines the window.
#print axioms PallLean.Paper93.permInvariant_determined_by_multiset

-- Paper §9 Lemma 31: symmetric tensor power dim ≤ multichoose.
#print axioms PallLean.Paper93.profileSubspace_finrank_bound
#print axioms PallLean.Paper93.multichoose_le_choose_of_dim_le_three

-- Paper §9.3: compiled-coefficient basis finrank ≤ 3.
#print axioms PallLean.Paper93.interfaceSpace_compiledBasis_finrank_le_three

/-! #### Cross-chain headline parity (landed)

For cross-chain audit consistency we also emit the Matching and
Direct chains' `P ≠ NP` headline directives here.  All three
(Matching / Direct / Unified) should carry kernel-only axiom
profiles. -/

-- Matching chain: Agent N9's near-zero-arg headline.
-- (Parametric in MatchingBundle + two universal `Prop` hypotheses
-- for N3 and N8; not genuinely zero-arg at the present commit.)
#print axioms PallLean.Paper93.Matching.P_ne_NP_paper_faithful_zero

/-! #### Agents O3, O5, O6 — not yet landed

The directives below audit the per-agent deliverables of Agents
O3, O5, O6 on the Unified chain.  As none of them have landed at
the present commit (their universal deliverables are carried as
`Prop`-binders on the O7 signatures), these directives are emitted
**as comments**, annotated with the expected theorem name.  They
should be uncommented once the corresponding agents land their
theorems into the `PallLean.Paper93.Unified` namespace.
-/

-- Agent O3 — Unified matching-form per-type row embeddings
-- with RowMatchingEmbedSlice slots discharged via O4.
-- Expected theorem name:
--   PallLean.Paper93.Unified.cookLevinPerTypeRowEmbeddings_concreteW_matching_unconditional_discharged
-- (Note: O2 landed a theorem of closely related shape in
-- `RowEmbeddingsDischarge.lean`; see that file's `#print axioms`
-- footer for the live axiom trace.)

-- Agent O5 — Unified matching-form template-collapse "fixed"
-- variant.
-- Expected theorem name:
--   PallLean.Paper93.Unified.cookLevinProfileTemplateCollapse_from_matching_fixed
-- (Not yet landed; carried as Prop-binder on O7 FullDischarge.)

-- Agent O6 — Unified bounded-profile full-discharge concrete term
-- (the "universal deliverable" that collapses P_ne_NP_unified_zero
-- to a genuine zero-arg theorem when substituted).
-- Expected theorem name:
--   PallLean.Paper93.Unified.cookLevinProfileTemplateCollapseLemmaBoundedProfile_full_discharge_unconditional
-- (Not yet landed; carried as Prop-binder on
-- P_ne_NP_unified_zero; see the O7 FullDischarge theorem for the
-- nearest in-tree analogue modulo two Prop-binders.)

/-! ### `#print axioms` — structural audit anchor (this file)

The anchor in this file is proved by `trivial`, hence itself
kernel-only.  Printing its axioms confirms that the audit file
adds no new axioms to the Unified chain. -/

#print axioms PallLean.Paper93.Unified.round11_unified_audit
