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

## Sound NP-side encoding (2026-04-15)

The characteristic-polynomial PD route (NP-side of Theorem 140) had
**inconsistent axioms** due to `parity_odd` in `TseitinFormula` forcing the
characteristic polynomial to be identically 0.

**Fix (RamanujanTseitin.lean §11)**: Added `SoundTseitinEncoding` that drops
`charPoly_eq_characteristic` and uses an abstract characteristic polynomial
with only structural constraints (multilinear, base-variable-only). This
matches the paper's actual construction with even-parity Tseitin formulas.

### Sound NP-side axiom inventory

| Axiom | File | Status | Paper |
|-------|------|--------|-------|
| `sound_characteristic_pd_row_derivs` | RamanujanTseitin | CONSISTENT axiom | §14.1 |
| `sound_tseitin_pdMatrix_lower_bound_small` | RamanujanTseitin | CONSISTENT axiom | finite range |
| `sound_lps_family_exists` | RamanujanTseitin | sorry | §6 LPS |

### Sound NP-side proof chain

```
sound_lps_family_exists (sorry: LPS construction)
     ↓
SoundRamanujanTseitinFamily
     ↓
disjoint_packing_exists (PROVED: greedy algorithm)
     ↓
buildKroneckerSystem (PROVED: combinatorial)
     ↓
sound_characteristic_pd_row_derivs (AXIOM: row realization)
     ↓
sound_characteristic_pd_rows_mem (PROVED: rows ∈ pdColumnSpace)
     ↓
sound_tseitin_pdMatrix_lower_bound (PROVED for n≥660; AXIOM n<660)
     ↓
sound_theorem72_condensed (PROVED: condensed existential)
     ↓
pdMatrix_le_spdpRank (PROVED: Lemma 69)
     ↓
theorem_140_sound_decomposition (PROVED: connects to charPolyRank)
```

### Connection to Separation29

`theorem_140_sound_decomposition` (Separation29.lean) shows how the monolithic
axiom `theorem_140_np_side` follows from:
1. The sound PD-matrix lower bound (`sound_theorem72_condensed`)
2. The proved Lemma 69 (`pdMatrix_le_spdpRank`)
3. A bridge linking `spdpRank` to the abstract `charPolyRank`

The remaining gap (step 3) is a definition-level identification, not a deep
theorem.

## Route B paper-faithful semantic front (2026-04-15, updated)

### Current live Route B packaging status (2026-04-15, honest tracker update)

The semantic delta under direct audit here is the live
`PallLean/GodMoveCore.lean` edit. The shared tree also has concurrent tracked
changes in nearby Route B files, but this note is only classifying the current
`GodMoveCore` movement. That movement is a **semantic interface refactor**, not
a shell-cleanup pass.

What the in-flight edit is trying to make explicit:

- `GodMoveRouteB_TargetData`: packages the hard-instance bookkeeping together
  with the extraction-facing coupled-sheet target
- `GodMoveRouteB_ExtractionTransfer`: names the DecidesSAT-dependent rank
  transfer separately from the NP-side lower-bound package
- `GodMoveRouteB_ExtractionObligation`: is now just the factored transfer seam
  on `GodMoveExtractionTarget`

Why this matters semantically:

- the old Route B records bundled hard-instance data, target polynomial data,
  and NP lower bounds in a way that made it easy for status text to slide into
  talking as if the entire weakened separation shell had advanced
- the live refactor makes the real theorem boundary sharper:
  NP-side progress and extraction-side progress are different kinds of work
- this is a genuine semantic-tracker improvement because it separates:
  1. target-side / NP-side data packaging
  2. the still-load-bearing DecidesSAT extraction seam
  3. the downstream wrapper theorems consuming those pieces

Honest current state of that refactor:

- it is **not landed cleanly yet**
- `~/.elan/bin/lake env lean PallLean/GodMoveCore.lean` currently fails
- the present failures are migration-level semantic bookkeeping issues, not
  shell cleanup:
  - duplicate doc-comment blocks before `GodMoveExtractionTarget` and
    `GodMoveRouteB_TargetData`
  - `routeB_from_semantic_gap` still constructs the old flat
    `GodMoveRouteB_Obligations` fields instead of the new `extractionTarget`
    field
- so the honest inventory claim is:
  the branch is refining the Route B theorem/interface inventory, but there is
  **no new cleanly validated theorem milestone to count from this delta yet**

### New structures and theorems

**GodMoveCore.lean** additions:
- `ExtractionRestrictionStage`: typed restriction with rank monotonicity
- `ExtractionProjectionStage`: typed projection with rank monotonicity
- `ExtractionMapDecomposition`: three-stage extraction map composite
- `extraction_from_decomposition`: compositionality lemma (0 custom axioms)
- `GodMoveSemanticGap`: narrowest semantic frontier for Route B
- `GodMoveRouteB_TargetData`: shared Route B hard-instance plus
  extraction-target package
- `GodMoveRouteB_ExtractionTransfer`: factored name for the extraction-side
  rank-transfer claim
- `GodMoveRouteB_WeakenedObligations`: uses n^(log n/4) instead of C(n/3, log n)
- `separation_from_weakened_routeB`: separation from weakened Route B (0 custom axioms)
- `RouteBNPFromPdMatrix`: PD-matrix NP data with explicit bridge gap
- `routeB_weakened_np_from_pdMatrix`: derives NP bound from PD data (0 custom axioms)

**Separation29.lean** additions:
- `ConcreteNPSideData`: packages sound encoding output for separation
- `ConcretePSideData`: packages DecidesSAT-dependent P-side data
- `separation_from_concrete_data`: axiom-free separation theorem (0 custom axioms)
- `concreteNPSideData_spdp_lower`: PD→SPDP transfer for concrete data
- `theorem_140_from_concrete`: discharge Thm 140 via concrete NP data
- `theorem_139_from_concrete`: discharge Thm 139 via concrete P data

**RamanujanTseitin.lean** additions:
- `SingleClauseDerivWitness`: clause-local derivative realization
- `sound_single_clause_deriv_realization`: Sub-axiom A (§14 Lemma 95)
- `DisjointClauseCompositionWitness`: disjoint clause composition
- `sound_disjoint_clause_composition`: Sub-axiom B (§14 Lemma 97)
- `sound_row_derivs_from_decomposition`: reconstruction (sorry'd)
- `sound_tseitin_pdMatrix_lower_bound_trivial`: n < 16 sub-range (exponent = 0)
- `sound_tseitin_pdMatrix_lower_bound_mid`: axiom for n ∈ [16, 256)
- `sound_tseitin_pdMatrix_lower_bound_hard`: axiom for n ∈ [256, 660)

### Updated NP-side axiom decomposition

The monolithic `sound_characteristic_pd_row_derivs` decomposes into:
1. `sound_single_clause_deriv_realization` — clause-local derivative (genuine algebraic core)
2. `sound_disjoint_clause_composition` — Leibniz composition (should be provable from 1)

The finite range `sound_tseitin_pdMatrix_lower_bound_small` decomposes into:
1. Trivial sub-range [6, 16): exponent = 0, bound is 1 ≤ rank (sorry'd)
2. Mid sub-range [16, 256): axiom, exponent = 1
3. Hard sub-range [256, 660): axiom, exponent = 2

### Restriction monotonicity front (Lemma 141 support)

The nearby P-side support file `RestrictionMono.lean` now has an explicit
coefficient-matrix route instead of the older opaque submodule-image sketch.

New theorem-level infrastructure:
- `CoeffMatrixHelpers.coeffVector`, `coeffVectorLin`, `coeffMatrix`
- `CoeffMatrixHelpers.monomialActionMatrix`
- `CoeffMatrixHelpers.rank_coeffMatrix_map_le`
- `CoeffMatrixHelpers.finrank_span_eq_matrix_rank`
- `RestrictionMono.coeffVector_applyRestriction_eq_sum_restrictionColumns`
- `RestrictionMono.restriction_image_spdpSubspace_finrank_le_spdpRank`
- `RestrictionMono.restrictedSourceSpdpCoeffMatrix_rank_le`
- `RestrictionMono.freeRestrictedSpdpSubspace_le_restriction_image`
- `RestrictionMono.freeRestrictedSpdpSubspace_le_restrictedSpdpSubspace`
- `RestrictionMono.freeRestrictedSpdpSubspace_finrank_le_restrictedSpdpRank`
- `RestrictionMono.freeRestrictedSpdpSubspace_finrank_le_spdpRank`
- `RestrictionMono.freeRestrictedSpdpCoeffMatrix_rank_le_spdpRank`

Current narrowed gap:
- no local `sorry` remains in `RestrictionMono.lean`
- the honest remaining issue for Lemma 141 is semantic rather than a proof
  placeholder: the ambient target of `applyRestriction ρ f` still allows
  multiplier monomials using fixed variables, so the paper's column-deletion
  argument does not directly match the current definitions
- the free-variable-only target subspace is now formalized, sits inside the
  honest ambient `spdpSubspace κ ℓ (applyRestriction ρ f)`, and is bounded by
  both the restricted-target rank and the original `spdpRank`
- what remains is the reverse inclusion/equality identifying that ambient
  restricted target with the paper-faithful free-variable-only target

So the local status is:
- `RestrictionMono.restriction_image_spdpSubspace_finrank_le_spdpRank`:
  theorem proved
- `RestrictionMono.restrictedSourceSpdpCoeffMatrix_rank_le_spdpRank`:
  theorem proved
- `RestrictionMono.freeRestrictedSpdpSubspace_finrank_le_restrictedSpdpRank`:
  theorem proved
- `RestrictionMono.freeRestrictedSpdpSubspace_finrank_le_spdpRank`:
  theorem proved
- `RestrictionMono.freeRestrictedSpdpCoeffMatrix_rank_le_spdpRank`:
  theorem proved
- `RestrictionMono.spdpRank_restriction_mono`: not currently the honest local
  theorem statement under the ambient definitions
- custom axioms in `RestrictionMono`: `0`
- remaining `sorry` in `RestrictionMono`: `0`
- semantic role: non-load-bearing for the current active contradiction, but
  still the right linear-algebra seam for decomposing the Route B / shell P-side

### Exact remaining gaps for Route B

1. **PD→blocked SPDP bridge** (`pd_to_blocked_transfer`): linear algebra
2. **Semantic extraction seam** (`GodMoveSemanticGap` plus the extraction obligation it feeds): genuine DecidesSAT-dependent frontier
3. **P-side compilation** (`compiled_rank_bound`): BP compilation

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
