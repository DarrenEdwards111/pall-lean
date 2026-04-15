# Formalization Status — `godmove-paper-faithful`

**Branch:** `godmove-paper-faithful`  
**Date:** 2026-04-15

## Current truth

The active route on this branch is the **latent compiler route**, not the older
paper-numbered `Separation29` shell.

The actual imported entrypoint is [PallLean.lean](/tmp/pall-lean/PallLean.lean),
which imports:

- `PallLean.LatentCompiler`
- `PallLean.LatentWidthRankDecomp`
- `PallLean.LatentWitnessMinorDecomp`
- `PallLean.LatentCompilerFinalRoute`

The active final contradiction theorem is:

- [PallLean/LatentCompilerFinalRoute.lean](/tmp/pall-lean/PallLean/LatentCompilerFinalRoute.lean):
  `LatentCompilerFinalRoute.P_neq_NP_latent_decomp`

This theorem is **axiom-free in Lean syntax**, but it is still **conditional on
an explicit assumptions bundle**:

- P-side obligation: `theorem216_p_obligation`

So the honest status is:

- global axioms on the active route: `0`
- active-route `sorry`: `0`
- explicit paper-facing obligations still required to close the route: `1`

## Active paper-facing frontier

The remaining mathematical frontier is packaged in
[PROOF-OBLIGATIONS.md](/tmp/pall-lean/PROOF-OBLIGATIONS.md).

At the top level there is **one** remaining external obligation:

1. `latent_profile_assembly_logscale`
   - P-side Width⇒Rank profile-assembly bound at log scale

The NP side is now built canonically inside the route from the selector
closed-form package, so it is no longer an external assumption on the active
final theorem.

## How this relates to the paper

The paper-level separation shell is still the right conceptual map:

- Theorem 139: P-side polynomial upper bound
- Theorem 140: NP-side exponential lower bound
- Lemma 141: restriction / submatrix monotonicity support

But on this branch those statements are **not** the active implementation
boundary. They are represented indirectly through the latent-route obligations
above.

Also:

- `charPolyRank` should be read as an interface symbol / abstraction barrier
- the substantive paper-level frontier is the proof of the upper/lower-bound
  theorems, not the opaque symbol itself
- `RestrictionMono` is structurally non-load-bearing on the current route, but
  still conceptually real mathematics rather than mere syntax cleanup
- LPS / Ramanujan existence is deep imported math and remains a reasonable
  axiom boundary when using the paper-numbered shell

## Historical files

The repo still contains older route/status files, including:

- `PallLean/Separation29.lean`
- `PallLean/SeparationAssembly.lean`
- `HANDOFF-fixed-profile-gap.md`

Those are useful for orientation, but they do **not** describe the current
active imported route.
