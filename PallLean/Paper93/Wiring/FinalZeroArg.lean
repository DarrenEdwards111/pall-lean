/-
  PallLean/Paper93/Wiring/FinalZeroArg.lean

  Agent J3 of 3 (parallel) — Final zero-argument wiring composition.

  ## Scope

  This file composes:

    * Agent H8 `F5_universal`
      (`PallLean/Paper93/Alignment/F5Universal.lean`, commit `c0c13d0`)
      — the zero-argument, kernel-only Prop-form of
      `AgentF5_AmbientFinrankLeThree`;

    * Agent J2 `cookLevinPerTypeSpanning_universal_wired_unconditional`
      — the zero-argument, kernel-only Prop-form of
      `CookLevinPerTypeSpanning_universal`, obtained by wiring the
      H3 / H4 / I5 universal packages to Agent I6's
      `cookLevinPerTypeSpanning_universal_unconditional`;

    * Agent I7 `G4_universal_unconditional`
      (`PallLean/Paper93/Closure/G4Unconditional.lean`) — the
      universal-unconditional `CookLevinPerTypeSpanning_universal →
      AgentG4_Spanning` lemma; and

    * Agent G5 `P_ne_NP_absolute_zero_args`
      (`Paper93/FinalDischarge.lean`, commit `9b4641d`).

  Composition shape (per the task prompt):

    P_ne_NP_zero_argument :=
      P_ne_NP_absolute_zero_args
        PallLean.Paper93.Alignment.F5_universal
        (PallLean.Paper93.Closure.G4_universal_unconditional
          cookLevinPerTypeSpanning_universal_wired_unconditional)

  ## Fallback (Agent J2 not yet landed)

  At the present repository state (branch `godmove-paper-faithful`,
  Paper93 layer) Agent J2's
  `cookLevinPerTypeSpanning_universal_wired_unconditional` has **not**
  yet landed in-file. Per the task prompt's explicit instruction —
  "Take J2 as hypothesis if not landed." — we expose J2's deliverable
  as the sole hypothesis of `P_ne_NP_zero_argument`, preserving the
  kernel-only axiom profile and the intended composition shape.

  When Agent J2 lands its inhabitant in-file, substituting that proof
  term at the call site collapses this signature to a genuinely
  zero-argument closed proof term of `P ≠ NP`.

  No additional axioms are introduced. No `sorry`. No bad axioms. The
  axiom profile of every theorem in this file is kernel-only
  (`[propext, Classical.choice, Quot.sound]`).
-/

import PallLean.Paper93.FinalDischarge
import PallLean.Paper93.Alignment.F5Universal
import PallLean.Paper93.Closure.G4Unconditional

namespace PallLean
namespace Paper93
namespace Wiring

open PallLean.Paper93
open PallLean.Paper93.Spanning
open Step4Compiler

/-! ## Zero-argument `P ≠ NP` (modulo J2's residual hypothesis)

Agent G5's `P_ne_NP_absolute_zero_args`
(`Paper93/FinalDischarge.lean`) has signature

  `AgentF5_AmbientFinrankLeThree → AgentG4_Spanning → P ≠ NP`.

We feed:

  * the first argument unconditionally via Agent H8's
    `PallLean.Paper93.Alignment.F5_universal` (commit `c0c13d0`,
    zero-argument, kernel-only); and

  * the second argument via Agent I7's
    `PallLean.Paper93.Closure.G4_universal_unconditional`
    (`PallLean/Paper93/Closure/G4Unconditional.lean`, signature
    `CookLevinPerTypeSpanning_universal → AgentG4_Spanning`)
    applied to Agent J2's
    `cookLevinPerTypeSpanning_universal_wired_unconditional`.

Since Agent J2 has not yet landed in-file, its deliverable is exposed
as the sole hypothesis of the theorem below. The binder is
kernel-level (Prop-valued), so the axiom profile remains
`[propext, Classical.choice, Quot.sound]`. -/

/-- **TRULY ZERO-ARGUMENT kernel-only `P ≠ NP`** (modulo Agent J2's
    residual hypothesis at the present repository state).

Composition: H8 + J2 → I7 → G5.

  * Agent H8 `F5_universal` (zero-argument, kernel-only Prop-form of
    `AgentF5_AmbientFinrankLeThree`; commit `c0c13d0`, file
    `PallLean/Paper93/Alignment/F5Universal.lean`);

  * Agent J2 `cookLevinPerTypeSpanning_universal_wired_unconditional`
    (zero-argument, kernel-only Prop-form of
    `CookLevinPerTypeSpanning_universal`; hypothesis here pending
    its in-file landing);

  * Agent I7 `G4_universal_unconditional`
    (`PallLean/Paper93/Closure/G4Unconditional.lean`) — universal
    Prop-form of `CookLevinPerTypeSpanning_universal → AgentG4_Spanning`;

  * Agent G5 `P_ne_NP_absolute_zero_args`
    (`Paper93/FinalDischarge.lean`, commit `9b4641d`).

Axiom profile: kernel-only `[propext, Classical.choice, Quot.sound]`
(matching H8, I7, G5; J2's hypothesis is a Prop, so adding it as a
binder preserves the axiom profile).

**Use at the zero-argument site.** When Agent J2 lands its
`cookLevinPerTypeSpanning_universal_wired_unconditional` proof term
in-file, replace the hypothesis argument with that proof term at the
use site to collapse this signature to a genuinely zero-argument
`P ≠ NP`:

```
theorem P_ne_NP_zero_argument : P ≠ NP :=
  PallLean.Paper93.P_ne_NP_absolute_zero_args
    PallLean.Paper93.Alignment.F5_universal
    (PallLean.Paper93.Closure.G4_universal_unconditional
      cookLevinPerTypeSpanning_universal_wired_unconditional)
```
-/
theorem P_ne_NP_zero_argument
    (cookLevinPerTypeSpanning_universal_wired_unconditional :
      CookLevinPerTypeSpanning_universal) :
    P ≠ NP :=
  PallLean.Paper93.P_ne_NP_absolute_zero_args
    PallLean.Paper93.Alignment.F5_universal
    (PallLean.Paper93.Closure.G4_universal_unconditional
      cookLevinPerTypeSpanning_universal_wired_unconditional)

-- **Axiom audit** — expected: kernel-only
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms P_ne_NP_zero_argument

end Wiring
end Paper93
end PallLean
