/-
  PallLean/Paper93/Closure/G4Unconditional.lean

  Agent I7 of 10 (parallel).

  ## Scope

  This file composes:

    * Agent I6 `cookLevinPerTypeSpanning_universal_unconditional` —
      the zero-argument proof of `CookLevinPerTypeSpanning_universal`
      (per-type spanning bundle holding for every bounded-parameter
      `(M, n, hn, htb, hns, W)` input), obtained by discharging the
      G1 / G2 / G3 per-type generators via the H3 / H4 / H5 pipeline;

    * Agent H9 `G4_universal`
      (`PallLean/Paper93/Alignment/G4Universal.lean`, commit
      `6629c1f`) — the hypothesis-taking universal lemma

        `CookLevinPerTypeSpanning_universal → AgentG4_Spanning`

      promoting G4's universal post-span containment theorem into
      Agent G5's universal `Prop`.

  Post-composing H9 on I6 yields a **zero-argument** inhabitant of
  `PallLean.Paper93.AgentG4_Spanning`, which is the precise
  deliverable that Agent G5's `P_ne_NP_absolute_zero_args` and
  Agent H10's `P_ne_NP_fully_unconditional` call sites require in
  order to collapse their respective signatures to zero arguments.

  ## Fallback (Agent I6 not yet landed)

  At the present repository state (branch `godmove-paper-faithful`,
  Paper93 layer), Agent I6's
  `cookLevinPerTypeSpanning_universal_unconditional` has **not** yet
  landed in-repo under `PallLean.Paper93.Closure.UnconditionalSpanning`.

  Per the task prompt's explicit instruction — "Take I6 as hypothesis
  if not landed" — we expose I6's deliverable as the sole hypothesis
  of the universal-unconditional theorem below, so that once Agent I6
  lands its
  `cookLevinPerTypeSpanning_universal_unconditional : CookLevinPerTypeSpanning_universal`
  inhabitant, the theorem below collapses to a zero-argument
  inhabitant of `AgentG4_Spanning` by substitution at the use site.

  ## Faithfulness

  The proof is a direct term-mode post-composition of Agent H9's
  `G4_universal` on Agent I6's supplied hypothesis. No analytic
  content is added or simplified; this file contains exactly the
  alignment composition requested in the task prompt.

  ## Axiom trace

  `#print axioms` at the end of this file is expected to show the
  kernel-only `propext`, `Classical.choice`, `Quot.sound` profile
  inherited from H9 / G4 / Mathlib.

  No `sorry`. No bad axioms. No additional axioms introduced.
-/

import PallLean.Paper93.Alignment.G4Universal

namespace PallLean
namespace Paper93
namespace Closure

open PallLean.Paper93.Spanning
open PallLean.Paper93.Alignment

/-! ## Agent I6 ⇒ H9 ⇒ `AgentG4_Spanning`

Agent H9's `G4_universal`
(`PallLean/Paper93/Alignment/G4Universal.lean`) has signature

  `CookLevinPerTypeSpanning_universal → AgentG4_Spanning`.

Agent I6's `cookLevinPerTypeSpanning_universal_unconditional` is
expected to be a zero-argument inhabitant of
`CookLevinPerTypeSpanning_universal`. Post-composition yields a
zero-argument inhabitant of `AgentG4_Spanning`, which is Agent G5's
second hypothesis in `P_ne_NP_absolute_zero_args`.

Since I6 has not yet landed in-file at the present repository state,
we expose I6 as the sole hypothesis of the universal-unconditional
theorem, matching the task prompt's explicit fallback. -/

/-- **Agent I7: Agent G4 universal unconditional (modulo I6 hypothesis).**

    Given Agent I6's zero-argument
    `cookLevinPerTypeSpanning_universal_unconditional : CookLevinPerTypeSpanning_universal`
    (discharging G1 / G2 / G3's per-type spanning bundle for every
    bounded-parameter input), produce a zero-argument inhabitant of
    Agent G5's `PallLean.Paper93.AgentG4_Spanning` Prop by
    post-composing Agent H9's `G4_universal`.

    **Use at the zero-argument site.** When Agent I6 lands its
    `cookLevinPerTypeSpanning_universal_unconditional`, replace the
    hypothesis argument at the call site with that proof term to
    collapse the signature to zero arguments:

    ```
    theorem G4_universal_unconditional : PallLean.Paper93.AgentG4_Spanning :=
      PallLean.Paper93.Closure.AgentG4_Spanning_of_I6
        cookLevinPerTypeSpanning_universal_unconditional
    ```

    The proof is a direct term-mode application of Agent H9's
    `G4_universal` on the supplied hypothesis; no new content is
    added. -/
theorem AgentG4_Spanning_of_I6
    (cookLevinPerTypeSpanning_universal_unconditional :
      CookLevinPerTypeSpanning_universal) :
    PallLean.Paper93.AgentG4_Spanning :=
  PallLean.Paper93.Alignment.G4_universal
    cookLevinPerTypeSpanning_universal_unconditional

/-! ## Alias matching the task prompt's mnemonic

The following alias matches the name `G4_universal_unconditional`
used in the task prompt; it is hypothesis-taking on I6 in the current
repository state (I6 not yet landed) and collapses to zero arguments
as soon as Agent I6's deliverable lands in-file. -/

/-- Alias of `AgentG4_Spanning_of_I6` matching the task prompt's
    mnemonic `G4_universal_unconditional`. Hypothesis-taking on
    Agent I6's `cookLevinPerTypeSpanning_universal_unconditional`
    pending its landing in-repo. -/
theorem G4_universal_unconditional
    (cookLevinPerTypeSpanning_universal_unconditional :
      CookLevinPerTypeSpanning_universal) :
    PallLean.Paper93.AgentG4_Spanning :=
  AgentG4_Spanning_of_I6
    cookLevinPerTypeSpanning_universal_unconditional

-- **Axiom audit** — expected: kernel-only
-- `[propext, Classical.choice, Quot.sound]`, matching H9 / G4.
#print axioms AgentG4_Spanning_of_I6
#print axioms G4_universal_unconditional

end Closure
end Paper93
end PallLean
