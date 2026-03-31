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
    - `npBridge : theorem223_extraction_obligation ...`
  - P part:
    - `pAsm : theorem216_p_obligation ...`

The route lemmas reassemble NP/P parts into the final contradiction chain using:
- `theorem223_extraction_obligation` (alias of `selector_bridge_logscale`)
- `latent_hard_witness_logscale` (assembled NP lower bound)
- `theorem216_p_obligation` (alias of `obligation2_p_logscale`)

---

## Obligation 1 (NP side)

### Name
`obligation1_np_logscale` (=`latent_hard_witness_logscale`)

Paper-faithful route: direct identity-minor lower bound on `latentCompiledPoly`.

**Key proved lemmas** (no longer assumptions):
- `pderiv_selSlot_machCopyGadget` — derivatives at selSlot positions kill machCopySheet
- `pderiv_selSlot_copyConGadget` — derivatives at selSlot positions kill copyConSheet

These are now **proved theorems** in `LatentWitnessMinorDecomp.lean`.
The remaining obligation is the assembled NP lower bound itself.

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
`obligation2_p_logscale` (=`latent_profile_assembly_logscale`)

Paper-faithful decomposition:
- Section 9 profile-count side:
  - `theorem9_profile_count_obligation` (=`latent_profile_count_logscale`)
- Section 9 within-profile dimension side:
  - `theorem9_within_profile_dim_obligation` (=`latent_within_profile_dim_logscale`)
- Assembled P-side upper bound:
  - `theorem216_p_obligation` (=`obligation2_p_logscale`)

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
