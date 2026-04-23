/-
  PallLean/Paper93/Specialized/FinalAudit.lean
  ============================================================================

  Agent L4 of 5 (parallel) — Final axiom-profile audit of the
  **specialised** Paper93 `P ≠ NP` chain routed through Agent J1's
  `concreteW` family.

  ## Purpose

  This file is the final audit anchor for the specialised chain
  (Agents L1 / L2 / L3 parallel stack). It performs one job only:

    * For every key theorem of the specialised chain, emit a
      `#print axioms` directive so that the Lean elaborator prints the
      exact axiom set transitively consumed by the elaborated proof
      term.

    * For a kernel-only proof, the expected axiom profile is:

          [propext, Classical.choice, Quot.sound]

      These three are the Lean 4 *kernel* axioms always available in
      any Lean 4 theory. No `sorryAx`, no bespoke `axiom`, and no
      `Classical.*` beyond `choice` should appear anywhere in the
      chain's transitive closure.

    * **Compare** the specialised chain's zero-argument headline
      against the universal (non-specialised) chain's Closure variant
      `PallLean.Paper93.Closure.P_ne_NP_truly_zero_args`
      (Agent I8, file `PallLean/Paper93/Closure/TrulyZeroArg.lean`,
      still carrying one residual universal-spanning hypothesis).

  ## Scope (Agent L4 of 5, parallel)

  Per the task prompt, this agent creates **only** this single file
  under `PallLean/Paper93/Specialized/FinalAudit.lean`. No other files
  are touched.

  ## Status of Agents L1 / L2 / L3 at the present repository state

  **None of the L1 / L2 / L3 target theorems have landed yet.** At the
  present commit (`godmove-paper-faithful @ ab6644e`, the head of the
  K1 / K2 parallel stack), no namespace
  `PallLean.Paper93.Specialized` has been introduced in-repo. The
  closest existing analogue is `PallLean.Paper93.TruZeroArg`
  (Agent K2, file `PallLean/Paper93/TruZeroArg.lean`) which already
  composes Agent H8's `F5_universal` with the discharge of Agent K1's
  `AgentG4_Spanning_concrete` via `concreteW`, yielding

    theorem P_ne_NP_truly_zero
        (hSpan_univ : CookLevinPerTypeSpanning_universal) : P ≠ NP

  i.e.\ `P ≠ NP` modulo the single universal per-type spanning
  hypothesis. Agents L1 / L2 / L3 are expected to package that
  universal hypothesis away to produce a genuinely zero-argument

    theorem P_ne_NP_via_concreteW_unconditional : P ≠ NP

  but the three L-stack deliverables

    * `PallLean.Paper93.Specialized.cookLevinProfileSubspace_at_concreteW_contains_postSpan`
      (Agent L1),
    * `PallLean.Paper93.Specialized.cookLevinProfileTemplateCollapseLemmaBoundedProfile_at_concreteW_discharged`
      (Agent L2),
    * `PallLean.Paper93.Specialized.P_ne_NP_via_concreteW_unconditional`
      (Agent L3),

  are not in-tree at this commit. Per the task prompt's fallback
  directive — "If L1/L2/L3 not landed, use their names in comments" —
  we therefore record the L1 / L2 / L3 target names as comments in the
  `#print axioms` block below, but cannot emit live elaborator
  directives against them (Lean would error on unresolved identifiers
  at elaboration time). The comparison `#print axioms` directive
  against the universal-chain variant
  `PallLean.Paper93.Closure.P_ne_NP_truly_zero_args` is, however,
  live; it audits the currently-landed reference-point for the
  residual hypothesis.

  ## Chain structure audited (specialised)

  The specialised Paper93 `P ≠ NP` chain, once Agents L1 / L2 / L3
  land, will have the following shape:

      Paper93 Closure (Agents I1–I8) + Alignment (H8, H9)
         │
         │   [universal-W content: F5_universal, G4_universal_unconditional,
         │    CookLevinPerTypeSpanning_universal, etc.]
         ▼
      Wiring/ConcreteW (Agent J1)
         │
         │   concreteW n hn4 σ — the canonical Fin 4 ↪ Fin n specialisation
         ▼
      Specialized/MlProj…  (Agent L1)
         │
         │   cookLevinProfileSubspace_at_concreteW_contains_postSpan
         ▼
      Specialized/TemplateCollapse… (Agent L2)
         │
         │   cookLevinProfileTemplateCollapseLemmaBoundedProfile_at_concreteW_discharged
         ▼
      Specialized/Final (Agent L3)
         │
         │   P_ne_NP_via_concreteW_unconditional
         ▼
      P ≠ NP (zero-argument, kernel-only)

  Each arrow corresponds to one or more theorems whose axiom profile
  should reduce to the kernel-only `[propext, Classical.choice,
  Quot.sound]`.

  ## Rules

    * **No `sorry`.** The two structural anchors
      `specialized_chain_audit` and `specialized_chain_summary` below
      are closed by `trivial`; all other content is declarative
      (`#print axioms` directives or comments).
    * **Kernel-only.** This file introduces no `axiom` declarations,
      no `noncomputable` defs, and no `Classical.*` invocations.
    * **No other files touched.** All `#print axioms` targets are
      referenced by fully-qualified name.
    * **Verified by `lake build`.**
-/

-- Closure layer reference point: the universal-chain variant of
-- `P ≠ NP` still carrying the residual universal spanning hypothesis.
-- This is the comparison target for the specialised zero-argument
-- chain (once Agents L1 / L2 / L3 land).
import PallLean.Paper93.Closure.TrulyZeroArg

-- K-stack reference points (already landed): the specialised chain's
-- immediate predecessors from which the L-stack is expected to
-- branch.
import PallLean.Paper93.TruZeroArg
import PallLean.Paper93.FinalCompositionV2
import PallLean.Paper93.Wiring.ConcreteW

namespace PallLean
namespace Paper93
namespace Specialized

/-! ## Structural audit anchors

Two named structural anchors for external tooling to reference by
stable name. Both proved by `trivial`, hence themselves kernel-only.

The truthful content of the audit is carried by the `#print axioms`
directives after the `end` blocks; these two theorems exist so that
external tooling has a stable symbol to pin the specialised chain
audit against.
-/

/-- **Audit anchor for the specialised chain.**

Structural marker recording that the specialised Paper93 `P ≠ NP`
chain (Agents L1 / L2 / L3, routed through Agent J1's `concreteW`
family) is expected to use only the three Lean 4 kernel axioms

    [propext, Classical.choice, Quot.sound]

and no `sorryAx`, no bespoke `axiom` declaration, no `Classical.*`
invocation beyond `Classical.choice`, and no SPDP profile generators.

The truthful content of this claim is carried by the `#print axioms`
directives at the end of this file (which are elaborator commands,
not proof obligations); this named theorem is a structural anchor
proved by `trivial` so that external tooling can refer to it by a
stable, kernel-only name. -/
theorem specialized_chain_audit : True := trivial

/-- **Summary anchor for the specialised chain.**

Structural marker summarising what the specialised chain is expected
to achieve once Agents L1 / L2 / L3 land, and what is currently
achieved at the present commit
(`godmove-paper-faithful @ ab6644e`):

  * **Achieved (K-stack).** Agent K2's
    `PallLean.Paper93.P_ne_NP_truly_zero` composes
    Agent H8's `F5_universal` with the discharge of Agent K1's
    `AgentG4_Spanning_concrete` via Agent J1's `concreteW` family,
    giving `P ≠ NP` modulo the single residual hypothesis
    `CookLevinPerTypeSpanning_universal`.

  * **Achieved (I-stack).** Agent I8's
    `PallLean.Paper93.Closure.P_ne_NP_truly_zero_args` gives
    `P ≠ NP` modulo the same single residual hypothesis
    `CookLevinPerTypeSpanning_universal`, via the universal-W
    pipeline.

  * **Not yet achieved (L-stack).** The specialised chain's target
    zero-argument theorem
    `PallLean.Paper93.Specialized.P_ne_NP_via_concreteW_unconditional`
    (Agent L3) is not in-tree at this commit. It is expected to
    package the residual `CookLevinPerTypeSpanning_universal`
    hypothesis away via Agents L1 / L2's `concreteW`-specialised
    post-span containment / template-collapse lemmas.

This theorem is a structural anchor proved by `trivial`, hence
kernel-only. -/
theorem specialized_chain_summary : True := trivial

end Specialized
end Paper93
end PallLean

/-! ### `#print axioms` — Specialised chain audit directives

Each directive below prints the axiom-set of one key theorem in the
specialised `P ≠ NP` chain. Expected output in every case:

    '<thm>' depends on axioms: [propext, Classical.choice, Quot.sound]

If any directive prints a larger list (e.g. `sorryAx`, a bespoke
`axiom` declaration, or a `Classical.*` beyond `choice`), the audit
fails.

---

#### L-stack target directives (Agents L1 / L2 / L3, **not yet landed**)

Per the task prompt's fallback directive ("If L1/L2/L3 not landed,
use their names in comments"), the three L-stack targets are
recorded as **comments** rather than live `#print axioms` directives
(which would fail elaboration on unresolved identifiers).

Once the corresponding theorems land, the comment markers below
should be converted to live `#print axioms` directives.

  -- Agent L3 — final zero-argument specialised headline:
  -- #print axioms PallLean.Paper93.Specialized.P_ne_NP_via_concreteW_unconditional

  -- Agent L2 — specialised template-collapse discharge:
  -- #print axioms
  --   PallLean.Paper93.Specialized.cookLevinProfileTemplateCollapseLemmaBoundedProfile_at_concreteW_discharged

  -- Agent L1 — specialised post-span containment at `concreteW`:
  -- #print axioms
  --   PallLean.Paper93.Specialized.cookLevinProfileSubspace_at_concreteW_contains_postSpan

---

#### Comparison target (universal chain, **already landed**)

This directive audits the currently-landed universal-chain variant
of `P ≠ NP`. Per the Closure `FinalAudit.lean`, its axiom profile
is `[propext, Classical.choice, Quot.sound]` — the kernel-only set.

Note: `PallLean.Paper93.Closure.P_ne_NP_truly_zero_args` is **not
zero-argument**; it takes one hypothesis
`CookLevinPerTypeSpanning_universal`. The specialised L3 target is
expected to package that hypothesis away, yielding a genuinely
zero-argument `P ≠ NP`.
-/

#print axioms PallLean.Paper93.Closure.P_ne_NP_truly_zero_args

/-! #### K-stack reference points (already landed)

These directives audit the K-stack predecessors from which the
L-stack is expected to branch. Expected axiom profile: kernel-only
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms PallLean.Paper93.P_ne_NP_truly_zero
#print axioms PallLean.Paper93.AgentG4_Spanning_concrete_discharged

/-! #### Structural audit anchors (this file)

The two anchors are proved by `trivial`, hence themselves
kernel-only. -/

#print axioms PallLean.Paper93.Specialized.specialized_chain_audit
#print axioms PallLean.Paper93.Specialized.specialized_chain_summary
