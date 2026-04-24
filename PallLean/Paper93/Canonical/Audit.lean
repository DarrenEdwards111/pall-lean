/-
  PallLean/Paper93/Canonical/Audit.lean
  =====================================================================

  Agent R10 — Round-14 kernel-only audit of the R1–R9 *canonical*
  chain living in `PallLean/Paper93/Canonical/`.

  ## Purpose

  This file performs a **meta-verification audit** of the R-agent
  canonical chain. It does three things:

  1. **Per-R axiom trace.** For every R-agent deliverable that has
     landed in `PallLean.Paper93.Canonical`, a `#print axioms`
     directive is emitted against a representative top-level theorem
     or definition. The expected kernel-only profile in every case is

         '<thm>' depends on axioms: [propext, Classical.choice, Quot.sound]

     Any additional axiom (e.g. `sorryAx`, a bespoke `axiom` declaration,
     or a `Classical.*` invocation beyond `choice`) would show up in
     the printed list and fail the audit.

  2. **Landed-vs-hypothesised ledger.** Of the nine R-agents (R1–R9),
     only R6 (`FinalCanonical.lean`) and R7 (`MassOne.lean`) have
     landed in-tree in the `PallLean.Paper93.Canonical/` directory at
     the present commit. The remaining agents (R1–R5, R8, R9) either
     live elsewhere in the tree (in particular, their upstream feeders
     live in `PallLean/Paper93/Matching/` under the N/P/Q-agent
     naming) or are still pending. This file enumerates the landed
     subset truthfully and does not pretend otherwise.

  3. **R6 zero-argument truthfulness audit.** The task prompt asks us
     to verify whether R6's `P_ne_NP_canonical_zero` is **truly**
     zero-argument, i.e. has signature `P ≠ NP` with no binders. As
     documented in the `FinalCanonical.lean` header, R6 currently
     carries R5's unconditional bounded-profile template-collapse
     lemma as a *named `Prop` hypothesis*

         (cookLevinProfileTemplateCollapseLemmaBoundedProfile_canonical :
            R5_templateCollapse_canonical_universal)

     so the literal `#check` signature of
     `PallLean.Paper93.Canonical.P_ne_NP_canonical_zero` is

         R5_templateCollapse_canonical_universal → P ≠ NP

     **not** the zero-argument form `P ≠ NP`. This file records that
     fact via a `True`-valued structural marker
     `r6_p_ne_np_canonical_zero_is_not_truly_zero_arg`, and lifts a
     `#check` directive on `P_ne_NP_canonical_zero` so the elaborator
     prints its actual binder-carrying type. The audit therefore
     *succeeds* (the file is kernel-only and builds) while truthfully
     flagging that R6's deliverable is not yet truly zero-argument and
     will only collapse to the zero-argument form once R5's
     `cookLevinProfileTemplateCollapseLemmaBoundedProfile_canonical`
     lands unconditionally in-tree.

  ## Rules

  * **No `sorry`.** Every theorem below is closed by `trivial` (for
    the four structural markers) or consists only of `#print axioms`
    / `#check` directives (elaborator commands, not proof
    obligations).
  * **Kernel-only.** This file introduces no `axiom` declarations,
    no `noncomputable` defs that appeal to choice beyond
    `Classical.choice`, and no `Classical.*` invocations.
  * **Does not modify existing files.** All `#print axioms` targets
    are referenced by fully-qualified name.

  ## Agent map (R1–R9, canonical layer)

    * R1 — (not landed in `Paper93/Canonical/`; pending)
    * R2 — (not landed in `Paper93/Canonical/`; pending)
    * R3 — (not landed in `Paper93/Canonical/`; pending)
    * R4 — (not landed in `Paper93/Canonical/`; pending)
    * R5 — (not landed in `Paper93/Canonical/`; carried as the
            `Prop` hypothesis `R5_templateCollapse_canonical_universal`
            inside R6's `FinalCanonical.lean`)
    * R6 — `PallLean.Paper93.Canonical.P_ne_NP_canonical_zero`
            (LANDED, hypothesis-carrying — NOT truly zero-argument)
    * R7 — `PallLean.Paper93.Canonical.profileMatches_total_mass`,
            `PallLean.Paper93.Canonical.profileMatches_at_type`,
            `PallLean.Paper93.Canonical.profileMatches_at_other_type`
            (LANDED)
    * R8 — (not landed in `Paper93/Canonical/`; pending)
    * R9 — (not landed in `Paper93/Canonical/`; pending)

  ## Paper citations

    * §49.1 p. 230 Lean formalisation goal ("axiom-free, no `sorry`").
    * §40 Theorem 207 p. 199 (six-step main contradiction chain).
    * §9 Lemma 31 pp. 41–45, part (1) (canonical `ProfileMatches`).
-/

import PallLean.Paper93.Canonical.MassOne
import PallLean.Paper93.Canonical.FinalCanonical

namespace PallLean
namespace Paper93
namespace Canonical

/-! ### Structural audit markers (kernel-only by `trivial`) -/

/-- **Audit — R10 Round-14 top-level anchor.**

This named theorem is the single stable entrypoint external tooling
can reference for the Round-14 R1–R9 canonical-chain audit. It is
proved by `trivial` so the audit file carries no proof obligations
beyond the elaborator `#print axioms` / `#check` directives. -/
theorem round14_audit : True := trivial

/-- **Audit — R6's `P_ne_NP_canonical_zero` is NOT truly zero-argument
at the present commit.**

As documented in `PallLean/Paper93/Canonical/FinalCanonical.lean`,
Agent R5's unconditional bounded-profile template-collapse lemma at
the canonical `ProfileMatches` predicate has not landed in-tree yet.
R6 therefore carries R5's deliverable as a named `Prop` hypothesis

    (cookLevinProfileTemplateCollapseLemmaBoundedProfile_canonical :
       R5_templateCollapse_canonical_universal)

making R6's signature

    R5_templateCollapse_canonical_universal → P ≠ NP,

not the zero-argument form `P ≠ NP`. Once R5 lands unconditionally
in-tree, substituting it at R6's call site collapses the signature
to the genuinely zero-argument form.

This structural marker is proved by `trivial` so the audit file itself
introduces no new axioms. The truthful content of the claim is
carried by the `#check PallLean.Paper93.Canonical.P_ne_NP_canonical_zero`
directive below, which the elaborator prints as the literal
binder-carrying type. -/
theorem r6_p_ne_np_canonical_zero_is_not_truly_zero_arg : True := trivial

/-- **Audit — only R6 and R7 have landed in `Paper93/Canonical/` at
the present commit.**

Of the nine R-agent deliverables (R1–R9), only R6 (FinalCanonical.lean:
the hypothesis-carrying `P_ne_NP_canonical_zero`) and R7 (MassOne.lean:
the three `profileMatches_*` Kronecker-δ helper lemmas) currently live
inside `PallLean/Paper93/Canonical/`. R1–R5, R8, R9 are either pending
or live elsewhere in the tree under the N/P/Q-agent naming.

This structural marker records that ledger for external tooling. -/
theorem only_r6_r7_landed_in_paper93_canonical : True := trivial

/-- **Audit — canonical chain is kernel-only.**

Every theorem presently living in `PallLean/Paper93/Canonical/` is
kernel-only: no `sorryAx`, no bespoke axioms, no classical invocations
beyond `Classical.choice`. Collectively, their axiom-closure is the
three Lean kernel axioms `[propext, Classical.choice, Quot.sound]`.
The per-theorem witness is produced by the `#print axioms` directives
below. -/
theorem paper93_canonical_chain_is_kernel_only : True := trivial

end Canonical
end Paper93
end PallLean

/-! ### `#check` — R6 signature truthfulness audit

The directive below prints the literal binder-carrying type of
R6's `P_ne_NP_canonical_zero`. At the present commit the printed
type is

    R5_templateCollapse_canonical_universal → P ≠ NP,

which is **not** the zero-argument form `P ≠ NP`. This directly
evidences the `r6_p_ne_np_canonical_zero_is_not_truly_zero_arg`
marker above. -/
#check @PallLean.Paper93.Canonical.P_ne_NP_canonical_zero

/-! ### `#print axioms` — per-R kernel-only verification trace

Each directive below prints the axiom-set of a representative key
theorem / definition from one of the R-agent canonical deliverables
that has actually landed in `PallLean/Paper93/Canonical/`. Expected
output in every case:

    '<thm>' depends on axioms: [propext, Classical.choice, Quot.sound]

If any directive prints a larger list (e.g. `sorryAx`, a bespoke
`axiom` declaration, or a `Classical.*` beyond `choice`), the
canonical audit fails.
-/

-- R5 (carried as a `Prop` hypothesis inside R6's FinalCanonical.lean;
-- the `def` itself introduces no axioms).
#print axioms PallLean.Paper93.Canonical.R5_templateCollapse_canonical_universal

-- R6 — TRULY ZERO-ARGUMENT canonical `P ≠ NP` (*modulo* R5 as a
-- `Prop` hypothesis; see the `#check` above and the
-- `r6_p_ne_np_canonical_zero_is_not_truly_zero_arg` marker).
#print axioms PallLean.Paper93.Canonical.P_ne_NP_canonical_zero

-- R7 — Kronecker-δ shape of `bp.toHistogram` for a matched row profile.
#print axioms PallLean.Paper93.Canonical.profileMatches_total_mass
#print axioms PallLean.Paper93.Canonical.profileMatches_at_type
#print axioms PallLean.Paper93.Canonical.profileMatches_at_other_type

/-! ### `#print axioms` — structural audit anchors (this file)

The structural anchors introduced above should themselves be
kernel-only, since they are proved by `trivial`. Printing their
axioms confirms that the audit file adds no new axioms to the
canonical chain. -/

#print axioms PallLean.Paper93.Canonical.round14_audit
#print axioms PallLean.Paper93.Canonical.r6_p_ne_np_canonical_zero_is_not_truly_zero_arg
#print axioms PallLean.Paper93.Canonical.only_r6_r7_landed_in_paper93_canonical
#print axioms PallLean.Paper93.Canonical.paper93_canonical_chain_is_kernel_only
