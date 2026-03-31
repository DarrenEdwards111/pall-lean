# PROOF-OBLIGATIONS (Active Latent Route)

This file tracks the **only remaining paper-facing obligations** on the active proof path.

## Active Entry Point

`PallLean.lean` imports:
- `PallLean.LatentCompiler`
- `PallLean.LatentWidthRankDecomp`
- `PallLean.LatentWitnessMinorDecomp`
- `PallLean.LatentCompilerFinalRoute`

## Final Theorem

- `LatentCompilerFinalRoute.P_neq_NP_latent_decomp`

This theorem is now **axiom-free** in Lean syntax and depends on an explicit assumptions bundle:

- `LatentCompilerFinalRoute.LogscaleObligations`
  - NP parts:
    - `npLower : extracted_witness_exp_lower_logscale ...`
    - `npBridge : selector_bridge_logscale ...`
  - P part:
    - `pAsm : latent_profile_assembly_logscale ...`

(Internal route still documents `latent_profile_count_logscale` and
`latent_within_profile_dim_logscale`, but these are currently discharged
trivially inside the assembly lemma and are not required from callers.)

The route lemmas reassemble NP/P parts into the final contradiction chain using:
- `theorem223_extraction_obligation` (alias of `selector_bridge_logscale`)
- `latent_hard_witness_logscale` (assembled NP lower bound)
- `theorem216_p_obligation` (alias of `latent_profile_assembly_logscale`)

---

## Obligation 1 (NP side)

### Name
`obligation1_np_logscale` (=`latent_hard_witness_logscale`)

Paper-faithful decomposition:
- Theorem 18-style identity-minor side:
  - `theorem18_identity_minor_obligation` (=`extracted_witness_exp_lower_logscale`)
- Theorem 223 extraction side:
  - `theorem223_extraction_obligation` (=`selector_bridge_logscale`)

### Location
`PallLean/LatentWitnessMinorDecomp.lean`

### Statement shape
At contradiction scale (`n ≥ 2^804`, `κ = log₂ n`):

`n^(κ/4) ≤ Γ_{κ,κ}(latentCompiledPoly)`

### Paper meaning
This is the NP hardness side (identity-minor / extracted witness lower bound) specialized to log-scale parameters.

---

## Obligation 2 (P side)

### Name
`theorem216_p_obligation` (=`latent_profile_assembly_logscale`)

### Location
`PallLean/LatentWidthRankDecomp.lean`

### Statement shape
At contradiction scale (`n ≥ 2^804`, `κ = log₂ n`):

`Γ_{κ,κ}(latentCompiledPoly) ≤ n^200`

### Paper meaning
This is the Width⇒Rank assembly side (profile count × within-profile dimension) specialized to the same log-scale parameters.

---

## Why this is compliant

The final contradiction theorem now uses:

1. NP lower bound at log-scale,
2. P upper bound at log-scale,
3. numeric separation (`n^200 < n^(log₂ n / 4)` for `n ≥ 2^804`).

No hidden global axioms are required in the active files. The two obligations are explicit assumptions in theorem arguments.

---

## Reviewer checklist

To close the route completely, provide proofs of:

- [ ] `latent_hard_witness_logscale`
- [ ] `latent_profile_assembly_logscale`

Once both are proved, `P_neq_NP_latent_decomp` is fully discharged without extra assumptions.
