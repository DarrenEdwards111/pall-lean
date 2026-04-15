# Handoff: Active paper-facing gaps on `godmove-paper-faithful`

Current branch: `godmove-paper-faithful`

## Scope correction

This handoff describes the **current active imported route** only.

It does **not** describe the older `Separation29` / `SeparationAssembly` shell,
and it does **not** treat older God-Move wrappers as the active final route.

The active entrypoint is:

- [PallLean.lean](/tmp/pall-lean/PallLean.lean)

The active final contradiction theorem is:

- [PallLean/LatentCompilerFinalRoute.lean](/tmp/pall-lean/PallLean/LatentCompilerFinalRoute.lean):
  `LatentCompilerFinalRoute.P_neq_NP_latent_decomp`

## Honest current state

The active route compiles without global axioms and without active-route
`sorry`, but the final theorem is still conditional on an explicit assumptions
bundle:

- NP-side obligation:
  `selCon_kronecker_data_logscale`
- P-side obligation:
  `theorem216_p_obligation`

So the live frontier is an **explicit two-obligation boundary**, not a claim
that the whole route is completely discharged.

## Remaining obligations

### 1. NP-side obligation

Name:

- `latent_hard_witness_logscale`

Meaning:

- direct identity-minor / Kronecker-data lower bound on
  `latentCompiledPoly` at contradiction scale

Primary file:

- [PallLean/LatentWitnessMinorDecomp.lean](/tmp/pall-lean/PallLean/LatentWitnessMinorDecomp.lean)

What is already in place:

- selector derivative hit/miss infrastructure
- iterated derivative closed forms on finite selCon products
- row scaffolding for Kronecker assembly
- choose-rank closure and numeric closure infrastructure

What remains:

- complete the coefficient-law / Kronecker-data assembly so the direct NP lower
  bound is fully proved rather than passed in as data

### 2. P-side obligation

Name:

- `latent_profile_assembly_logscale`
  (packaged to callers as `theorem216_p_obligation`)

Meaning:

- log-scale Width⇒Rank profile assembly bound for `latentCompiledPoly`

Primary file:

- [PallLean/LatentWidthRankDecomp.lean](/tmp/pall-lean/PallLean/LatentWidthRankDecomp.lean)

What is already in place:

- Section 9 profile-count side is discharged in-route
- within-profile dimension side is discharged in-route
- the profile-data package is explicit

What remains:

- the final profile assembly step turning those ingredients into the full
  `≤ n^200` log-scale rank bound

## How this relates to the paper shell

For paper-faithful orientation, the conceptual shell is still:

- Theorem 140: NP-side exponential lower bound
- Theorem 139: P-side polynomial upper bound
- Lemma 141: restriction / submatrix monotonicity support

But on this branch those are best viewed as the **paper-level interpretation**
of the active latent obligations, not as the live implementation boundary.

Also:

- `charPolyRank` is an abstraction symbol, not substantive theorem content
- `RestrictionMono` is not mere bookkeeping, even when non-load-bearing
- LPS / Ramanujan existence remains deep imported mathematics on the older
  paper-numbered shell

## Recommendation for the next agent

Stay on the latent route.

Best next moves:

1. NP side:
   finish the Kronecker coefficient-law assembly in
   `LatentWitnessMinorDecomp.lean`
2. P side:
   finish the final profile-assembly theorem in
   `LatentWidthRankDecomp.lean`

Do not spend a session “cleaning up status” by reviving older shell files as if
they were the active route. That is how the documentation drift happened.
