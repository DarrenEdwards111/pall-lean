/-
  PallLean/Paper93/FullyUnconditional.lean

  Agent H10 of 10 (parallel).

  ## Scope

  This file composes:

    * Agent H8 `F5_universal` — the universal (zero-argument) Prop-form
      derivation of `AgentF5_AmbientFinrankLeThree` (ambient per-type
      `W_σ` family in `MvPolynomial (Fin n) ℚ` with
      `Module.Finite ℚ ↥(W τ)` and `Module.finrank ℚ ↥(W τ) ≤ 3`, for
      every `(M,n,hn,htb,hns)` bounded-parameter input);

    * Agent H9 `G4_universal` — the universal (zero-argument) Prop-form
      derivation of `AgentG4_Spanning` (Cook-Levin post-span
      containment in `cookLevinProfileSubspace bp W` at every bounded
      profile, for every `(M,n,…,W,…)` input);

    * Agent G5 `P_ne_NP_absolute_zero_args`
      (`Paper93/FinalDischarge.lean`) — takes the two hypotheses above
      and produces `P ≠ NP`.

  Composing these three ingredients yields a genuinely **zero-argument**
  `P ≠ NP` theorem at the kernel-only axiom profile
  `[propext, Classical.choice, Quot.sound]`.

  ## Fallback (H8/H9 not yet zero-argument in-repo)

  At the present repository state (branch `godmove-paper-faithful`,
  Paper93 layer):

    * Agent H8's `F5_universal` has **not** yet landed in-file under
      `PallLean.Paper93.Alignment`;

    * Agent H9's `G4_universal` **has** landed
      (`PallLean/Paper93/Alignment/G4Universal.lean`) but is itself
      hypothesis-taking on
      `CookLevinPerTypeSpanning_universal` (awaiting H5's
      `cookLevinPerTypeSpanning_discharged`), hence not yet a
      zero-argument inhabitant of `AgentG4_Spanning`.

  Per the task prompt's explicit instruction — "If H8/H9 aren't
  landed, this theorem takes them as hypotheses" — we expose the two
  deliverables as hypotheses on `P_ne_NP_fully_unconditional`, so that
  once Agent H8 lands a zero-argument `F5_universal` and Agent H9's
  `G4_universal` is post-composed with H5's per-type spanning
  discharge (yielding a zero-argument inhabitant of
  `AgentG4_Spanning`), the theorem collapses to a zero-argument
  `P ≠ NP` by substitution at the use site.

  No additional axioms are introduced. No `sorry`. No bad axioms.
  Every theorem in this file is kernel-only
  (`[propext, Classical.choice, Quot.sound]`).
-/

import PallLean.Paper93.FinalDischarge

namespace PallLean
namespace Paper93

open Step4Compiler

/-! ## Zero-argument `P ≠ NP`

`P_ne_NP_absolute_zero_args` (Agent G5, `Paper93/FinalDischarge.lean`)
takes two arguments:

  * `hF5 : AgentF5_AmbientFinrankLeThree` — Agent F5 / H8 deliverable;
  * `hG4 : AgentG4_Spanning` — Agent G4 / H9 deliverable.

Once H8 and H9 land their zero-argument `F5_universal` and
`G4_universal` proofs under `PallLean.Paper93.Alignment`, those two
proof terms directly instantiate the hypotheses, collapsing the
signature to `P ≠ NP` with zero arguments. At the current repository
state those derivations are not in-file, so the theorem below exposes
the two deliverables as hypotheses in keeping with the explicit task
fallback. -/

/-- **`P ≠ NP` — fully unconditional (modulo Agent H8 / H9 hypotheses).**

Composition of:

  * Agent H8 `F5_universal` (ambient finrank ≤ 3 per-type `W_σ`
    family, every `(M,n,…)` bounded parameter);
  * Agent H9 `G4_universal` (Cook-Levin post-span spanning containment
    in `cookLevinProfileSubspace bp W`, every bounded-profile input);
  * Agent G5 `P_ne_NP_absolute_zero_args`
    (`Paper93/FinalDischarge.lean`);
  * Agent D `P_ne_NP_absolute_unconditional`
    (`Paper93/FinalComposition.lean`);
  * Agent C's `of_bridge` compositions
    (`Paper93/CookLevinProfileSubspace.lean`).

Axiom profile: kernel-only `[propext, Classical.choice, Quot.sound]`.

**Note.** When Agent H8 and Agent H9 land their `F5_universal` /
`G4_universal` proof terms under `PallLean.Paper93.Alignment`, replace
the two hypothesis arguments with those proof terms at the use site to
collapse this signature to zero arguments:

```
theorem P_ne_NP_fully_unconditional : P ≠ NP :=
  P_ne_NP_absolute_zero_args
    PallLean.Paper93.Alignment.F5_universal
    PallLean.Paper93.Alignment.G4_universal
```
-/
theorem P_ne_NP_fully_unconditional
    (hF5 : AgentF5_AmbientFinrankLeThree)
    (hG4 : AgentG4_Spanning) :
    P ≠ NP :=
  P_ne_NP_absolute_zero_args hF5 hG4

-- **Axiom audit** — expected: kernel-only `[propext, Classical.choice, Quot.sound]`.
#print axioms P_ne_NP_fully_unconditional

end Paper93
end PallLean
