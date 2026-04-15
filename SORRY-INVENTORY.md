# Formalization Status — `godmove-paper-faithful`

**Branch:** `godmove-paper-faithful`  
**Date:** 2026-04-15

## Current truth

The active route on this branch is the **latent compiler route**, not the older
paper-numbered `Separation29` shell and not the paper's primary God-Move shell.

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

- P-side obligation: `latent_profile_assembly_logscale`

So the honest status is:

- global axioms on the active route: `0`
- active-route `sorry`: `0`
- explicit paper-facing obligations still required to close the route: `1`

But the honest **paper-faithfulness** status is slightly different:

- faithful to a genuine paper route: yes
- closest to the direct separation route / Route A: yes
- fully faithful to the full paper emphasis, where Route B / Global God-Move is primary: no, not yet

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

Also, the desktop paper presents two routes:

- Route A: direct separation on an explicit NP witness family
- Route B: Global God-Move route

The paper treats Route B as primary. The active imported Lean route on this
branch is therefore only **partially** paper-faithful to the paper as a whole:
it tracks a genuine route in the paper, but not the paper's current primary
top shell.

Also:

- `charPolyRank` should be read as an interface symbol / abstraction barrier
- the substantive paper-level frontier is the proof of the upper/lower-bound
  theorems, not the opaque symbol itself
- `RestrictionMono` is structurally non-load-bearing on the current route, but
  still conceptually real mathematics rather than mere syntax cleanup
- LPS / Ramanujan existence is deep imported math and remains a reasonable
  axiom boundary when using the paper-numbered shell

## Critical finding: spdp_profile_generators is provably false (2026-04-15)

The axiom `spdp_profile_generators` (SymmetricPower.lean) is provably
inconsistent with the axiom-free NP-side theorem
`GodMoveReal.compiled_np_lower_bound_any_dtm`. The formal inconsistency
witness is `PaperFaithfulSeparation.spdp_profile_generators_inconsistent_with_np_side`.

**What was found**:

- The NP-side lower bound `C(n/3, log n) ≤ mlBlockedSpdpRank B κ ℓ (compiledPoly T)`
  is proved WITHOUT axioms and WITHOUT using DecidesSAT. It holds for ALL DTMs.
- The P-side axiom claims `mlBlockedSpdpRank B κ ℓ (compiledPoly T) ≤ n^200`
  for ALL DTMs (same partition, same κ = ℓ = log₂ n, same polynomial).
- Together: C(n/3, log n) ≤ n^200 — false for large n (C ≈ 2^{638000} vs n^200 = 2^{160800}).

**Root cause**: The profile compression axiom (paper §9, Theorem 92) classifies
derivatives by constraint-TYPE histogram. All booleanity derivatives at
first-of-block positions have the SAME profile. The axiom bounds within-profile
dimension by (log n + 1)^8, but the NP-side proves these generators are linearly
independent, giving within-profile dimension = C(n/3, log n) >> (log n + 1)^8.

**Impact on active routes**:

- Route B (PaperFaithfulSeparation): derives False from the false axiom.
  The semantic gap (DecidesSAT unused) means the proof doesn't follow the
  paper's actual argument. See GodMoveSemanticInterface for the correct seam.
- Latent route (LatentCompilerFinalRoute): the P-side obligation
  `latent_profile_assembly_logscale` likely faces the same issue, since it
  depends on the same profile compression idea.

## Historical files

The repo still contains older route/status files, including:

- `PallLean/Separation29.lean`
- `PallLean/SeparationAssembly.lean`
- `PallLean/PaperFaithfulSeparation.lean`
- `PallLean/GodMoveCore.lean`
- `PallLean/GodMoveReal.lean`
- `HANDOFF-fixed-profile-gap.md`

Those are useful for orientation, but they do **not** describe the current
active imported route.
