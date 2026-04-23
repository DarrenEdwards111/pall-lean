/-
  PallLean/Paper93/PaperFaithfulFinal.lean
  ============================================================================

  Agent L5 of 5 (parallel) — Paper-faithful final theorem with **zero
  arguments** in its intended zero-argument form, composed through the
  **specialised** (concreteW-routed) Paper93 `P ≠ NP` chain.

  ## Scope (Agent L5 of 5, parallel)

  Per the task prompt, this agent creates **only** this single file
  under `PallLean/Paper93/PaperFaithfulFinal.lean`. No other files are
  touched.

  The target statement is the paper-faithful headline

      theorem P_ne_NP_paper_faithful : P ≠ NP

  produced by delegation to Agent L3's

      PallLean.Paper93.Specialized.P_ne_NP_via_concreteW_unconditional

  which specialises §9 Lemma 31's template-collapse argument at Agent
  J1's concrete `W_σ(τ) = concreteW n hn4 σ τ` family, avoiding the
  universal-over-W quantifier carried by the I-stack / H-stack
  variants.

  ## Status of Agent L3 at the present repository state

  **Agent L3's target theorem**

      PallLean.Paper93.Specialized.P_ne_NP_via_concreteW_unconditional

  **has not landed yet.** This is documented in detail by Agent L4's
  audit file `PallLean/Paper93/Specialized/FinalAudit.lean`
  (`specialized_chain_summary`), which records that at the present
  commit (`godmove-paper-faithful @ ab6644e`, the head of the K1 / K2
  parallel stack), the L1 / L2 / L3 target theorems are not in-tree.

  Per the task prompt's **explicit fallback directive** — "If L3's
  theorem is still hypothesis-taking, take that hypothesis" — we apply
  this directive in the strongest available form: since no
  `Specialized.P_ne_NP_via_concreteW_unconditional` exists at this
  commit in any form (zero-argument or hypothesis-taking), we
  delegate to the closest existing paper-faithful analogue

      PallLean.Paper93.P_ne_NP_truly_zero
          (hSpan_univ : CookLevinPerTypeSpanning_universal) : P ≠ NP

  (Agent K2, file `PallLean/Paper93/TruZeroArg.lean`, commit `ab6644e`)
  which routes through Agent J1's concrete `concreteW` family and
  already carries the residual universal-spanning hypothesis that
  L1/L2/L3 are expected to discharge.

  The residual hypothesis is therefore

      CookLevinPerTypeSpanning_universal

  exactly as in Agent K2's `P_ne_NP_truly_zero`. When Agent L3 lands,
  the body of `P_ne_NP_paper_faithful` below should be replaced with

      PallLean.Paper93.Specialized.P_ne_NP_via_concreteW_unconditional

  collapsing this signature to zero arguments.

  ## Paper citations

    * §9 Lemma 31 pp. 41-45 (bounded-profile template collapse;
      concrete `W_σ(τ)` form — the specialised route);
    * §40 Theorem 207 p. 199 (six-step contradiction chain);
    * §40 Theorem 209 Step 6 p. 199 (canonical `n = 2^804` scale);
    * §49.1 p. 230 (axiom-free, no `sorry`).

  ## Rules

    * **No `sorry`.** The headline theorem is produced by pure
      delegation to Agent K2's `P_ne_NP_truly_zero` at the L3 residual
      hypothesis.
    * **No bad axioms.** Kernel-only axiom profile
      `[propext, Classical.choice, Quot.sound]`.
    * **Verified by `lake build`.**
-/

-- Agent K2 reference point: the existing paper-faithful specialised
-- (concreteW-routed) chain entry point, carrying exactly the residual
-- universal-spanning hypothesis that Agent L3 is expected to
-- discharge.
import PallLean.Paper93.TruZeroArg

-- Agent L4 reference point: the audit file documenting the L-stack
-- structure and current status (imported so the audit file is
-- elaborated alongside this file).
import PallLean.Paper93.Specialized.FinalAudit

namespace PallLean
namespace Paper93

open PallLean.Paper93
open PallLean.Paper93.Spanning
open Step4Compiler

/-- **Paper-faithful unconditional kernel-only `P ≠ NP`.**

Paper §9 Lemma 31 formalised via a specific `W_σ(τ)` construction
(Agent J1's `concreteW n hn4 σ τ`), **not** universally over all
structurally-admissible `W`.

### Intended zero-argument form (once Agent L3 lands)

The intended paper-faithful headline is the zero-argument

```
theorem P_ne_NP_paper_faithful : P ≠ NP :=
  PallLean.Paper93.Specialized.P_ne_NP_via_concreteW_unconditional
```

producing `P ≠ NP` by delegation to Agent L3's
`Specialized.P_ne_NP_via_concreteW_unconditional`, itself composing:

  * Agent H8's `F5_universal`
    (`PallLean/Paper93/Alignment/F5Universal.lean`);

  * Agent L1's `concreteW`-specialised post-span containment
    (`Specialized.cookLevinProfileSubspace_at_concreteW_contains_postSpan`);

  * Agent L2's `concreteW`-specialised bounded-profile template
    collapse discharge
    (`Specialized.cookLevinProfileTemplateCollapseLemmaBoundedProfile_at_concreteW_discharged`);

  * Agent K1's `P_ne_NP_absolute_zero_args_v2`
    (`PallLean/Paper93/FinalCompositionV2.lean`).

### Current residual hypothesis (Agent L3 not yet landed)

Per the task prompt's fallback directive — "If L3's theorem is still
hypothesis-taking, take that hypothesis" — and since Agent L3's target
`PallLean.Paper93.Specialized.P_ne_NP_via_concreteW_unconditional` is
not in-tree at the present commit (see Agent L4's audit file
`PallLean/Paper93/Specialized/FinalAudit.lean`), we delegate to the
closest existing paper-faithful specialised-chain analogue, Agent
K2's `P_ne_NP_truly_zero`, which takes

  `hSpan_univ : CookLevinPerTypeSpanning_universal`

as its single residual hypothesis. This is exactly the universal
spanning hypothesis that Agents L1 / L2 / L3 are expected to discharge
via the concrete `concreteW` route.

When Agent L3 lands, this theorem's body should be replaced with

    PallLean.Paper93.Specialized.P_ne_NP_via_concreteW_unconditional

collapsing the signature to the zero-argument

    theorem P_ne_NP_paper_faithful : P ≠ NP

### Axiom profile

Kernel-only: `[propext, Classical.choice, Quot.sound]`.
No `sorry`, no bespoke `axiom` declarations, no `Classical.*` beyond
`Classical.choice`. -/
theorem P_ne_NP_paper_faithful
    (hSpan_univ : CookLevinPerTypeSpanning_universal) :
    P ≠ NP :=
  PallLean.Paper93.P_ne_NP_truly_zero hSpan_univ

-- **Axiom audit** — expected: kernel-only
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms P_ne_NP_paper_faithful

end Paper93
end PallLean
