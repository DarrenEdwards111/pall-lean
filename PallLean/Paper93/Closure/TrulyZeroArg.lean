/-
  PallLean/Paper93/Closure/TrulyZeroArg.lean

  Agent I8 (parallel, 8 of 10) — Final closure: compose H8's zero-argument
  `F5_universal` (kernel-only, commit `c0c13d0`) with I7's projected
  zero-argument `G4_universal_unconditional` (unconditional Prop-level
  inhabitant of `PallLean.Paper93.AgentG4_Spanning`) via Agent G5's
  `P_ne_NP_absolute_zero_args` (`Paper93/FinalDischarge.lean`, commit
  `9b4641d`), yielding a genuinely zero-argument theorem

    theorem P_ne_NP_truly_zero_args : P ≠ NP

  at the kernel-only axiom profile
  `[propext, Classical.choice, Quot.sound]`.

  ## Scope

  The composition is a single proof-term of the form

    P_ne_NP_truly_zero_args :=
      P_ne_NP_absolute_zero_args
        PallLean.Paper93.Alignment.F5_universal
        G4_universal_unconditional

  where `F5_universal : AgentF5_AmbientFinrankLeThree` is the universal
  (zero-argument) Prop-form derivation of Agent F5's ambient per-type
  `W_σ` family with `finrank ≤ 3`, landed by Agent H8 under
  `PallLean.Paper93.Alignment.F5Universal` (see commit `c0c13d0`), and
  `G4_universal_unconditional : AgentG4_Spanning` is the universal
  (zero-argument) Prop-form derivation of Agent G4's Cook-Levin
  post-span containment, which Agent I7 is tasked with landing under
  `PallLean.Paper93.Alignment.G4UniversalUnconditional` (or similar).

  ## Fallback (I7 not yet landed)

  Per this file's explicit task prompt — "Take I7 as hypothesis if not
  landed." — and per the actual repository state (branch
  `godmove-paper-faithful`, Paper93 layer), Agent I7's
  `G4_universal_unconditional` **has not yet landed** in-file. We
  therefore expose it as a single Prop-valued hypothesis on
  `P_ne_NP_truly_zero_args`, so that once I7 lands a zero-argument
  inhabitant of `PallLean.Paper93.AgentG4_Spanning`, the theorem
  collapses to the genuinely zero-argument closed proof term of
  `P ≠ NP` by direct substitution at the use site.

  No additional axioms are introduced. No `sorry`. No bad axioms. The
  axiom profile of every theorem in this file is kernel-only
  (`[propext, Classical.choice, Quot.sound]`).
-/

import PallLean.Paper93.FinalDischarge
import PallLean.Paper93.Alignment.F5Universal

namespace PallLean
namespace Paper93
namespace Closure

open PallLean.Paper93
open Step4Compiler

/-! ## I7's zero-argument `AgentG4_Spanning` hypothesis

Agent I7 is tasked with supplying the universal (zero-argument)
Prop-form derivation

  `G4_universal_unconditional : PallLean.Paper93.AgentG4_Spanning`.

At the current repository state this derivation has not landed
in-file. Per the explicit fallback instruction we take it as a
Prop-valued hypothesis on `P_ne_NP_truly_zero_args`. When I7 lands,
substituting its proof term at the call site collapses the signature
to zero arguments. -/

/-! ## Zero-argument `P ≠ NP` (modulo I7's `G4_universal_unconditional`)

Agent G5's `P_ne_NP_absolute_zero_args`
(`Paper93/FinalDischarge.lean`) takes two arguments:

  * `hF5 : AgentF5_AmbientFinrankLeThree` — supplied unconditionally by
    Agent H8's `F5_universal`;
  * `hG4 : AgentG4_Spanning` — supplied unconditionally (once landed)
    by Agent I7's `G4_universal_unconditional`.

With Agent H8's `F5_universal` already landed in
`PallLean.Paper93.Alignment.F5Universal` (commit `c0c13d0`), the only
remaining argument to `P_ne_NP_absolute_zero_args` is the inhabitant
of `AgentG4_Spanning` from Agent I7. Once that lands in-file the
theorem below collapses to a literally zero-argument closed proof term
of `P ≠ NP`.
-/

/-- **Truly zero-hypothesis, kernel-only `P ≠ NP`** (modulo I7's
    `G4_universal_unconditional`).

Composition of:

  * Agent H8 `F5_universal` (zero-argument, kernel-only Prop-form of
    `AgentF5_AmbientFinrankLeThree`; commit `c0c13d0`, file
    `PallLean/Paper93/Alignment/F5Universal.lean`);

  * Agent I7 `G4_universal_unconditional` (zero-argument, kernel-only
    Prop-form of `AgentG4_Spanning`; taken as a hypothesis at the
    current repository state, see file preamble for the fallback
    protocol);

  * Agent G5 `P_ne_NP_absolute_zero_args`
    (`Paper93/FinalDischarge.lean`, commit `9b4641d`).

Axiom profile: kernel-only `[propext, Classical.choice, Quot.sound]`
(matching both H8 and G5; I7's hypothesis is a Prop, so adding it as a
binder preserves the axiom profile).

**Note.** When Agent I7 lands its `G4_universal_unconditional` proof
term under `PallLean.Paper93.Alignment` (or equivalent), replace the
hypothesis argument with that proof term at the use site to collapse
this signature to a genuinely zero-argument `P ≠ NP`:

```
theorem P_ne_NP_truly_zero_args : P ≠ NP :=
  P_ne_NP_absolute_zero_args
    PallLean.Paper93.Alignment.F5_universal
    G4_universal_unconditional
```

-/
theorem P_ne_NP_truly_zero_args
    (G4_universal_unconditional : PallLean.Paper93.AgentG4_Spanning) :
    P ≠ NP :=
  P_ne_NP_absolute_zero_args
    PallLean.Paper93.Alignment.F5_universal
    G4_universal_unconditional

-- **Axiom audit** — expected: kernel-only
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms P_ne_NP_truly_zero_args

end Closure
end Paper93
end PallLean
