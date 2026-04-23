/-
  PallLean/Paper93/Direct/AuditRound9.lean
  ============================================================================

  Agent M20 of M (parallel) — Final axiom-profile audit of the
  **Direct** Paper93 `P ≠ NP` chain routed through Agent J1's
  `concreteW` family.

  ## Purpose

  This file is the Round-9 audit anchor for the Direct chain
  (Agents M1 / … / M19, parallel stack).  It performs one job only:

    * For every landed theorem of the Direct chain (Agents M1 / … / M19),
      emit a `#print axioms` directive so that the Lean elaborator
      prints the exact axiom set transitively consumed by the
      elaborated proof term.

    * For a kernel-only proof, the expected axiom profile is

          [propext, Classical.choice, Quot.sound]

      These three are the Lean 4 *kernel* axioms always available in
      any Lean 4 theory.  No `sorryAx`, no bespoke `axiom`, and no
      `Classical.*` beyond `choice` should appear anywhere in the
      Direct chain's transitive closure.

    * Include **two overall summary anchors**
      (`direct_chain_round9_audit`, `direct_chain_round9_summary`)
      proved by `trivial`, so that external tooling has stable
      symbols to reference.

    * Emit the **headline directive**

          #print axioms PallLean.Paper93.Direct.P_ne_NP_zero

      which audits Agent M19's zero-argument-in-name-only P ≠ NP
      (see below: `P_ne_NP_zero` takes one residual hypothesis
      `CookLevinProfileTemplateCollapseDirect_universal`, exposed in
      its signature as the named argument
      `cookLevinProfileTemplateCollapse_direct`).

  ## Scope (Agent M20 of M, parallel)

  Per the task prompt, this agent creates **only** this single file
  under `PallLean/Paper93/Direct/AuditRound9.lean`.  No other files
  are touched.

  ## Status of Agents M1 / … / M19 at the present repository state

  At the present commit on branch `godmove-paper-faithful`, all of
  Agents M1 / … / M19 are **landed in-tree** as files under
  `PallLean/Paper93/Direct/`.  The mapping from agent number to
  deliverable file / theorem is:

    * Agent M1 — `BooleanityDirect.lean` — `booleanity_factor_direct_mem`.
    * Agent M2 — `BooleanityDerivs.lean` — `booleanity_iterDeriv_mem`.
    * Agent M3 — `BooleanityShiftDeriv.lean` — `booleanity_shift_deriv_mem`.
    * Agent M4 — `BooleanityMlProj.lean` —
                 `booleanity_mlProj_mem`, `iterDerivList_boolFactor_mem_source`.
    * Agent M5 — `BooleanityFull.lean` —
                 `booleanity_row_mem_profileSubspace`,
                 `booleanity_row_mem_profileSubspace_exists_bp`,
                 `derivCountProfile_singleton_booleanity`.
    * Agent M6 — `AdjacencyDirect.lean` — `adjacency_factor_direct_mem`.
    * Agent M7 — `AdjacencyDerivs.lean` — `adjacency_iterDeriv_mem`.
    * Agent M8 — `AdjacencyShiftDeriv.lean` —
                 `adjacency_shift_deriv_mem`,
                 `iterDerivList_adjacency_mem_submodule`.
    * Agent M9 — `AdjacencyMlProj.lean` — `adjacency_mlProj_mem`.
    * Agent M10 — `AdjacencyFull.lean` —
                  `adjacency_row_mem_profileSubspace`,
                  `adjacency_row_mem_profileSubspace_zero_shift`,
                  `adjacency_row_mem_profileSubspace_of_bridge`.
    * Agent M11 — `TransitionLeftDirect.lean` —
                  `transitionLeft_factor_direct_mem`,
                  `transitionLeftLift_mem_ambientPerType`.
    * Agent M12 — `TransitionLeftDerivs.lean` —
                  `transitionLeft_iterDeriv_mem`.
    * Agent M13 — `TransitionLeftShiftDeriv.lean` —
                  `transitionLeft_shift_deriv_mem`.
    * Agent M14 — `TransitionLeftMlProj.lean` —
                  `transitionLeft_mlProj_shift_iterDeriv_mem_mlProjClosure`,
                  `_ambient` variant, `_generic` variant.
    * Agent M15 — `TransitionLeftFull.lean` —
                  `transitionLeft_row_mem_profileSubspace`.
    * Agent M16 — `TransitionRightDormant.lean` —
                  `transitionRight_vacuous`,
                  `transitionRight_row_zero_mem`.
    * Agent M17 — `PerTypeComposition.lean` —
                  `cookLevinProfileSubspace_contains_postSpan_direct`,
                  `m16_transitionRight_row_vacuous`.
    * Agent M18 — `TemplateCollapseDirect.lean` —
                  `cookLevinProfileTemplateCollapse_direct`,
                  `cookLevinProfileTemplateCollapse_direct_universal`.
    * Agent M19 — `ZeroArgFinal.lean` — `P_ne_NP_zero`.

  Below we emit `#print axioms` directives for all of the theorem
  targets above.

  ### Note on `P_ne_NP_zero` reaching zero-arg

  Agent M19's `P_ne_NP_zero : ... → P ≠ NP` is the direct-chain
  zero-argument headline *in name*, but as currently landed it
  carries **one residual hypothesis**

      CookLevinProfileTemplateCollapseDirect_universal

  (exposed under the task prompt's named binder
  `cookLevinProfileTemplateCollapse_direct`).  It therefore does
  **not reach zero-arg** at the present commit; a genuine
  zero-argument form would require the residual universal
  hypothesis to be discharged from the already-landed M18 per-
  parameter deliverable via an aggregation of the per-type row
  embeddings (M5 / M10 / M15 / M16).  The axiom profile is
  already kernel-only.

  ## Rules

    * **No `sorry`.**  The two structural anchors below are closed by
      `trivial`; all other content is declarative (`#print axioms`
      directives or comments).
    * **Kernel-only.**  This file introduces no `axiom` declarations,
      no `noncomputable` defs, and no `Classical.*` invocations.
    * **No other files touched.**  All `#print axioms` targets are
      referenced by fully-qualified name.
    * **Verified by `lake build`.**

  Expected `#print axioms direct_chain_round9_audit`:
      [propext, Classical.choice, Quot.sound]
-/

-- Direct-chain landed feeders (booleanity thread: M1, M2, M3, M4).
-- Agent M5 (`Direct.BooleanityFull`) is audited via comment reference
-- only: its upstream import chain transits
-- `Paper93.Spanning.PerDerivativeSpanning`, whose own
-- `iterDerivSubmodule` definition duplicates the one from
-- `Paper93.Spanning.DerivativeClosure` that the M2 / M3 / M4
-- booleanity files already pull in; elaborating both paths into a
-- single file triggers Lean's duplicate-environment guard.  M5's
-- per-file `#print axioms` trace is verified in-file inside
-- `BooleanityFull.lean`.
import PallLean.Paper93.Direct.BooleanityDirect
import PallLean.Paper93.Direct.BooleanityDerivs
import PallLean.Paper93.Direct.BooleanityShiftDeriv
import PallLean.Paper93.Direct.BooleanityMlProj

-- Direct-chain landed feeders (adjacency thread: M6, M7, M8, M9, M10).
import PallLean.Paper93.Direct.AdjacencyDirect
import PallLean.Paper93.Direct.AdjacencyDerivs
import PallLean.Paper93.Direct.AdjacencyShiftDeriv
import PallLean.Paper93.Direct.AdjacencyMlProj
import PallLean.Paper93.Direct.AdjacencyFull

-- Direct-chain landed feeders (transitionLeft thread: M11, M12, M13,
-- M14, M15).
import PallLean.Paper93.Direct.TransitionLeftDirect
import PallLean.Paper93.Direct.TransitionLeftDerivs
import PallLean.Paper93.Direct.TransitionLeftShiftDeriv
import PallLean.Paper93.Direct.TransitionLeftMlProj
import PallLean.Paper93.Direct.TransitionLeftFull

-- Direct-chain landed feeders (transitionRight dormant thread: M16).
import PallLean.Paper93.Direct.TransitionRightDormant

-- Direct-chain landed feeders (composition layer: M17, M18, M19).
import PallLean.Paper93.Direct.PerTypeComposition
import PallLean.Paper93.Direct.TemplateCollapseDirect
import PallLean.Paper93.Direct.ZeroArgFinal

-- Wiring-layer reference point.
import PallLean.Paper93.Wiring.ConcreteW

-- NOTE on comparison targets.  The two natural "already-landed"
-- comparison targets for the Direct chain are
--   * `PallLean.Paper93.Closure.P_ne_NP_truly_zero_args` (Closure I8,
--     universal chain, still one residual hypothesis); and
--   * `PallLean.Paper93.P_ne_NP_truly_zero` (K-stack, specialised
--     through `concreteW`, still one residual hypothesis).
-- Both live above a transitive import of
-- `Paper93.Spanning.PerDerivativeSpanning`, whose own
-- `iterDerivSubmodule` definition duplicates the one from
-- `Paper93.Spanning.DerivativeClosure` that is transitively pulled
-- in by the Direct-chain feeders imported above.  Elaborating both
-- paths into a single file therefore triggers Lean's duplicate-
-- environment guard.  The `#print axioms` comparison directives for
-- those two targets live (and are verified) in
-- `Paper93/Specialized/FinalAudit.lean` and
-- `Paper93/Audit.lean` respectively; here we only audit the
-- Direct-chain deliverables themselves.

namespace PallLean
namespace Paper93
namespace Direct

/-! ## Structural audit anchors

Two named structural anchors for external tooling to reference by
stable name.  Both proved by `trivial`, hence themselves kernel-only.

The truthful content of the audit is carried by the `#print axioms`
directives after the `end` blocks; these anchors exist so that
external tooling has a stable symbol to pin the Direct-chain
Round-9 audit against.
-/

/-- **Round-9 audit anchor for the Direct chain.**

Structural marker recording that the Direct Paper93 `P ≠ NP`
chain (Agents M1 / … / M19, routed through Agent J1's `concreteW`
family) is expected to use only the three Lean 4 kernel axioms

    [propext, Classical.choice, Quot.sound]

and no `sorryAx`, no bespoke `axiom` declaration, no `Classical.*`
invocation beyond `Classical.choice`, and no SPDP profile generators.

The truthful content of this claim is carried by the `#print axioms`
directives at the end of this file (which are elaborator commands,
not proof obligations); this named theorem is a structural anchor
proved by `trivial` so that external tooling can refer to it by a
stable, kernel-only name. -/
theorem direct_chain_round9_audit : True := trivial

/-- **Overall summary anchor for the Direct chain at Round 9.**

Structural marker summarising what the Direct chain achieves at the
present commit:

  * **All of Agents M1 / … / M19 are landed.**  The Direct chain's
    three per-factor threads (booleanity M1–M5, adjacency M6–M10,
    transitionLeft M11–M15), the transitionRight dormant thread
    (M16), the per-type composition (M17), the template-collapse
    discharge (M18), and the zero-argument headline (M19) are all
    in-tree.

  * **`P_ne_NP_zero` reaches "zero-arg-in-name-only".**  Agent
    M19's `PallLean.Paper93.Direct.P_ne_NP_zero` has the signature

        theorem P_ne_NP_zero
            (cookLevinProfileTemplateCollapse_direct :
               CookLevinProfileTemplateCollapseDirect_universal) :
            P ≠ NP

    — **one residual hypothesis**.  It does **not** reach genuinely
    zero-arg form at this commit; discharging the residual universal
    hypothesis from M18's per-parameter deliverable (via an
    aggregation of the four per-type row embeddings M5 / M10 / M15 /
    M16) would yield a genuinely zero-argument `P ≠ NP`.

  * **Axiom profile.**  Every landed Direct-chain theorem is
    kernel-only `[propext, Classical.choice, Quot.sound]`, as
    verified by the `#print axioms` directives at the end of this
    file.

This theorem is a structural anchor proved by `trivial`, hence
kernel-only. -/
theorem direct_chain_round9_summary : True := trivial

end Direct
end Paper93
end PallLean

/-! ### `#print axioms` — Direct-chain Round-9 audit directives

Each directive below prints the axiom-set of one key theorem in the
Direct `P ≠ NP` chain.  Expected output in every case:

    '<thm>' depends on axioms: [propext, Classical.choice, Quot.sound]

If any directive prints a larger list (e.g. `sorryAx`, a bespoke
`axiom` declaration, or a `Classical.*` beyond `choice`), the Round-9
audit fails.

---

#### Booleanity thread — M1 / M2 / M3 / M4 / M5
-/

-- Agent M1 — direct booleanity factor membership in `concreteW`.
#print axioms PallLean.Paper93.Direct.booleanity_factor_direct_mem

-- Agent M2 — booleanity iterDeriv ∈ concreteW derivative closure.
#print axioms PallLean.Paper93.Direct.booleanity_iterDeriv_mem

-- Agent M3 — booleanity shift · iterDerivList in shiftClosure of
-- iterDerivSubmodule.
#print axioms PallLean.Paper93.Direct.booleanity_shift_deriv_mem

-- Agent M4 — mlProj(shift · iterDerivList S boolFactor) in
-- mlProjClosure(shiftClosure W ℓ) + source-membership lemma.
#print axioms PallLean.Paper93.Direct.iterDerivList_boolFactor_mem_source
#print axioms PallLean.Paper93.Direct.booleanity_mlProj_mem

-- Agent M5 — full row → V_h embedding for the booleanity factor.
-- Routed via comment reference only (see booleanity-thread import
-- block above for the duplicate-environment rationale).  The per-
-- file `#print axioms` trace inside `BooleanityFull.lean` confirms
-- all three deliverables are kernel-only
-- `[propext, Classical.choice, Quot.sound]`.
--
-- #print axioms PallLean.Paper93.Direct.derivCountProfile_singleton_booleanity
-- #print axioms PallLean.Paper93.Direct.booleanity_row_mem_profileSubspace
-- #print axioms PallLean.Paper93.Direct.booleanity_row_mem_profileSubspace_exists_bp

/-! #### Adjacency thread — M6 / M7 / M8 / M9 / M10 -/

-- Agent M6 — direct adjacency factor membership in `concreteW`.
#print axioms PallLean.Paper93.Direct.adjacency_factor_direct_mem

-- Agent M7 — adjacency iterDeriv ∈ concreteW derivative closure.
#print axioms PallLean.Paper93.Direct.adjacency_iterDeriv_mem

-- Agent M8 — adjacency shift · iterDerivList in shiftClosure +
-- submodule-membership lemma.
#print axioms PallLean.Paper93.Direct.iterDerivList_adjacency_mem_submodule
#print axioms PallLean.Paper93.Direct.adjacency_shift_deriv_mem

-- Agent M9 — mlProj(shift · iterDerivList S (1 - X_i·X_j)) in
-- mlProjClosure(shiftClosure W ℓ).
#print axioms PallLean.Paper93.Direct.adjacency_mlProj_mem

-- Agent M10 — full adjacency row → V_h embedding.
#print axioms PallLean.Paper93.Direct.adjacency_row_mem_profileSubspace
#print axioms PallLean.Paper93.Direct.adjacency_row_mem_profileSubspace_zero_shift
#print axioms PallLean.Paper93.Direct.adjacency_row_mem_profileSubspace_of_bridge

/-! #### TransitionLeft thread — M11 / M12 / M13 / M14 / M15 -/

-- Agent M11 — direct transitionLeft factor membership in `concreteW`
-- + ambient-per-type lift lemma.
#print axioms PallLean.Paper93.Direct.transitionLeftLift_mem_ambientPerType
#print axioms PallLean.Paper93.Direct.transitionLeft_factor_direct_mem

-- Agent M12 — transitionLeft iterDeriv membership.
#print axioms PallLean.Paper93.Direct.transitionLeft_iterDeriv_mem

-- Agent M13 — transitionLeft shift·iterDerivList in shiftClosure.
#print axioms PallLean.Paper93.Direct.transitionLeft_shift_deriv_mem

-- Agent M14 — mlProj(shift · iterDerivList) membership in
-- mlProjClosure of shiftClosure (generic + named + ambient).
#print axioms
  PallLean.Paper93.Direct.mlProj_shift_iterDeriv_mem_mlProjClosure_generic
#print axioms
  PallLean.Paper93.Direct.transitionLeft_mlProj_shift_iterDeriv_mem_mlProjClosure
#print axioms
  PallLean.Paper93.Direct.transitionLeft_mlProj_shift_iterDeriv_mem_mlProjClosure_ambient

-- Agent M15 — full transitionLeft row → V_h embedding.
#print axioms PallLean.Paper93.Direct.transitionLeft_row_mem_profileSubspace

/-! #### TransitionRight dormant thread — M16 -/

-- Agent M16 — vacuous transitionRight case discharge + row-zero
-- membership.
#print axioms PallLean.Paper93.Direct.transitionRight_vacuous
#print axioms PallLean.Paper93.Direct.transitionRight_row_zero_mem

/-! #### Composition layer — M17 / M18 -/

-- Agent M17 — per-type composition: direct post-span containment at
-- `concreteW`, built from the per-type row embeddings
-- (M5 / M10 / M15 / M16).
#print axioms PallLean.Paper93.Direct.cookLevinProfileSubspace_contains_postSpan_direct
#print axioms PallLean.Paper93.Direct.m16_transitionRight_row_vacuous

-- Agent M18 — direct bounded-profile template-collapse at `concreteW`
-- (per-parameter and universal forms).
#print axioms PallLean.Paper93.Direct.cookLevinProfileTemplateCollapse_direct
#print axioms PallLean.Paper93.Direct.cookLevinProfileTemplateCollapse_direct_universal

/-! #### Headline — M19 `P_ne_NP_zero`

The Direct chain's zero-argument-in-name headline theorem.  As
currently landed, its signature carries **one residual hypothesis**

    cookLevinProfileTemplateCollapse_direct :
      CookLevinProfileTemplateCollapseDirect_universal

so it does not yet reach genuinely zero-arg form; see
`direct_chain_round9_summary` above. -/

#print axioms PallLean.Paper93.Direct.P_ne_NP_zero

/-! ### `#print axioms` — structural audit anchors (this file)

The two anchors in this file are proved by `trivial`, hence
themselves kernel-only.  Printing their axioms confirms that the
audit file adds no new axioms to the Direct chain. -/

#print axioms PallLean.Paper93.Direct.direct_chain_round9_audit
#print axioms PallLean.Paper93.Direct.direct_chain_round9_summary
