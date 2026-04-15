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
  - P part:
    - `pAsm : theorem216_p_obligation ...` (paper-faithful profile-data package)

The route lemmas reassemble NP/P parts into the final contradiction chain using:
- `selCon_kronecker_data_logscale_from_canonical_idxList`
- `latent_hard_witness_logscale_from_kronecker`
- `latent_hard_witness_logscale` (NP lower bound)
- `theorem216_p_obligation` (alias of `obligation2_p_logscale`)

---

## NP Side

### Name
`obligation1_np_logscale` (=`latent_hard_witness_logscale`)

Paper-faithful route: direct identity-minor lower bound on `latentCompiledPoly`.

**Key proved structural lemmas** (no longer assumptions):
- `pderiv_selSlot_machCopyGadget`
- `pderiv_selSlot_copyConGadget`
- `iterDerivList_selSlot_machCopySheet_zero`
- `iterDerivList_selSlot_copyConSheet_zero`
- `iterDerivList_selSlot_latentCompiled_eq_selCon`
- `pderiv_selSlot_selConGadget_eq`
- `pderiv_selSlot_selConGadget_ne`
- `pderiv_selSlot_selConProd_of_mem`
- `pderiv_selSlot_selConProd_of_not_mem`
- `pderiv_selSlot_selConSheet`

These isolate selConSheet under nonempty selSlot-derivative lists and prove
selector-derivative hit/miss product rules on arbitrary finite selCon products.

New κ-level assembly theorems proved:
- `iterDeriv_selConProd_eq`
- `iterDeriv_selConSheet_eq`

This gives the closed-form iterated derivative formula over finite selCon products
and full `selConSheet`, matching the paper's product-derivative backbone.

New closure theorems proved:
- `selCon_choose_rank_logscale_from_matrix`
- `selCon_choose_rank_logscale_from_data`
- `selCon_kronecker_linear_independence_logscale_from_data_numeric`
- `selCon_kronecker_coeff_law_logscale_from_canonical_idxList`
- `selCon_kronecker_data_logscale_from_canonical_idxList`
- `selCon_kronecker_linear_independence_logscale_from_canonical_idxList`

Numeric choose closure is now proved internally (`selCon_choose_numeric_logscale_proved`).
The Kronecker coefficient data is now built canonically inside the active route,
so the NP side is no longer an external paper-facing obligation.

### Location
`PallLean/LatentWitnessMinorDecomp.lean`

### Statement shape
At contradiction scale (`n ≥ 2^804`, `κ = log₂ n`):

`n^(κ/4) ≤ Γ_{κ,κ}(latentCompiledPoly)`

### Paper meaning
This is the NP hardness side (identity-minor / extracted witness lower bound) specialized to log-scale parameters.

---

## Remaining Obligation (P side)

### Name
`obligation2_p_logscale` (=`latent_profile_assembly_logscale`)

Paper-faithful decomposition:
- Section 9 profile-count side:
  - `theorem9_profile_count_obligation` (=`latent_profile_count_logscale`)
  - proved in-route: `theorem9_profile_count_obligation_proved`
- Section 9 within-profile dimension side:
  - `theorem9_within_profile_dim_obligation` (=`latent_within_profile_dim_logscale`)
  - proved in-route: `theorem9_within_profile_dim_obligation_proved`
- Paper data package:
  - `theorem216_profile_data_logscale`
  - closure theorem: `obligation2_p_logscale_from_data`
- Assembled P-side upper bound (core remaining hard step):
  - `latent_profile_assembly_logscale` (alias path to `obligation2_p_logscale`)

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

No hidden global axioms are required in the active files. The only remaining explicit assumption on the active final route is the P-side package.

---

## Reviewer checklist

To close the route completely, provide proofs of:

- [ ] `latent_profile_assembly_logscale`

Once that is proved, `P_neq_NP_latent_decomp` is fully discharged without extra assumptions.
