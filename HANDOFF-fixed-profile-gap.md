# Handoff: Remaining theorem-sized gaps after fixed-profile bridge work

Current branch: `godmove-paper-faithful`
Current state: `lake build PallLean.SeparationFinal` passes, 0 live sorry in the active route.

## Remaining axioms

1. `PallLean/SymmetricPower.lean:582`
   - `axiom spdp_profile_generators`
   - This is the P-side profile-compression theorem.

2. `PallLean/GodMoveReal.lean:556`
   - `axiom identity_construction_np_lower_bound`
   - This is the NP-side lower-bound / identity-minor theorem.

## What was completed around the P-side seam

Substantial infrastructure was built in `PallLean/SymmetricPowerBound.lean` and compile-checked, including:

- fixed-profile cover assembly pipeline:
  - `FixedProfileGeneratorCover`
  - `FixedProfileCoverFamily`
  - `HasFixedProfileCoverFamily`
  - `rank_bound_of_hasFixedProfileCoverFamily`
- pointwise generator seam:
  - `SpdpGeneratorData`
  - `GeneratorProfileCandidate`
  - `GeneratorHasChosenFixedProfileCover`
  - `IsExtractedProfileCandidate`
- product-side extraction substrate:
  - `ProductSpdpGeneratorData`
  - `ProductDerivAssignmentWitness`
  - `ProductLeibnizExpansionWitness`
- compile-checked base cases:
  - zero-radius extraction chain
  - singleton-radius witness / extracted candidate

These make the missing P-side theorem much more explicit, but do **not** prove it.

## Key insight

The old route is:

`spdp_profile_generators`
→ `product_leibniz_profile_cover`
→ `leibniz_symmetric_power_descent_bound`
→ `rank_bound_from_fixed_profile_factorization`

The new infrastructure shows an alternate route is conceivable:

`HasFixedProfileCoverFamily`
→ `rank_bound_of_hasFixedProfileCoverFamily`
→ reroute `rank_bound_from_fixed_profile_factorization`

However, this does **not** remove the core mathematical difficulty. It just isolates it.

## Exact remaining P-side gap

To replace `spdp_profile_generators`, one must construct fixed-profile cover spaces with proved finrank bounds:

- for each admissible profile histogram `h`, produce a cover space
- prove `fixedProfileSpan terms h ≤ coverSpace`
- prove
  `Module.finrank ℚ coverSpace ≤ profileSymmetricDimBound W h`
- then assemble into `HasFixedProfileCoverFamily`

This is exactly the symmetric-power compression theorem.

### Why previous attempts stalled

Because the real missing fact is:

> the span of all `m`-fold products of vectors from a `d`-dimensional local space
> has dimension `C(m+d-1, d-1)`, not `d^m`

Formalizing that honestly in Lean seems to require several hundred lines of new symmetric/tensor-style algebra or an equivalent bespoke finite-dimensional span argument.

## Exact remaining NP-side gap

`identity_construction_np_lower_bound` still needs a formal lower-bound argument showing the compiled Cook-Levin polynomial contains / transfers the identity-minor style independent family needed for rank at least `C(n, log n)`.

This is a separate theorem-sized task and was not materially advanced here.

## Recommendation for the next agent

Do **not** add more wrapper structures unless they directly discharge one of these theorem obligations.

Best next move on the P-side:
1. stay in `PallLean/SymmetricPowerBound.lean`
2. formalize a genuine per-profile finite-dimensional span theorem for products from bounded local interface spaces
3. use that to build `FixedProfileGeneratorCover`
4. prove `HasFixedProfileCoverFamily`
5. only then reroute `rank_bound_from_fixed_profile_factorization`

Best next move on the NP-side:
- separate session, separate theorem campaign in `GodMoveReal.lean`

## Commits of note

- `c82f469` Add honest fixed-profile cover bridge scaffolding
- `056032b` Keep fixed-profile bridge seam explicit
- `38a3967` Refine pointwise fixed-profile bridge seams
- `30ea5c2` Add zero-radius product extraction base case
- `47c8ff0` Add product-level extraction witnesses
- `bc154f1` Revert sorry-based reroute attempt

## Warning

A previous attempt moved the gap from axiom to `sorry`. That was reverted. Do not repeat that. Axioms are currently the honest boundary.
