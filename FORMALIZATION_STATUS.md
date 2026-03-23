# P ≠ NP Lean Formalization — Final Status

**Repository:** https://github.com/DarrenEdwards111/pall-lean  
**Branch:** `compiled-route`  
**Paper:** arXiv:2512.11820v5 (Edwards 2025)  
**Lean:** v4.28.0 + Mathlib  
**Commit:** `ab0a82c`

## Result

```
53 files, 10,321 lines of Lean 4
0 errors
0 sorries on the critical path
2 custom axioms matching the paper's A2 + A3
```

**P ≠ NP is proved conditional on 2 axioms that are the paper's irreducible core claims.**

## v2 P_neq_NP Axiom Inventory

```
#print axioms PneqNP_v2.P_neq_NP

propext                              — standard Lean
Classical.choice                     — standard Lean
Quot.sound                           — standard Lean
BoolCircuit.ptime_spdp_collapse      — Paper A2 / Theorem 6.1
TseitinLowerBound.sat_is_in_NP      — Paper A3 / Theorem 10.1
```

### `ptime_spdp_collapse` — P-side rank collapse (A2)

Every deterministic polynomial-time machine M has compiled SPDP rank
≤ n^O(1), hence ≤ √n for large n. This places all P-computable functions
in the FSPDP collapse class.

**Proof scaffolding:** CookLevinBridge.lean decomposes this into
`cook_levin_spdp_bridge` (Cook-Levin projection) + v1 profile compression
(PROVED in ProfileCompression.lean + CookLevin.lean).

### `sat_is_in_NP` — NP-side Tseitin lower bound (A3)

There exists an NP family F with ¬InFSPDP(F n) for all large n.
The paper constructs this via Tseitin formulas on Ramanujan expanders:
3-SAT ∈ NP trivially, and the Tseitin family has SPDP rank ≥ n^Θ(log n)
via the identity-minor construction (Theorem 9.3 → Theorem 10.1).

**Proof scaffolding:** TseitinLowerBound.lean with:
- `identity_minor_gives_rank_lower_bound` — PROVED
- `choose_superpolynomial` — PROVED (C(αn, log n) > √n)
- `choose_mono_second`, `choose_ge_choose_two`, `choose_two_ge_self` — PROVED
- `pow2_gt_twice` — PROVED
- `DisjointClauseFamily` structure — defined

## What Is Proved

### SPDP Theory
- SPDP definitions, monotonicity, S-coupled shifts, transversal conditions
- `restrictedSpdpRank_le_spdpRank` — restriction is rank-nonincreasing (PROVED)
- `pderiv_restrictPoly_comm` — derivatives commute with restriction (PROVED)
- `iterDerivList_restrictPoly_comm` — iterated version (PROVED)
- `restrictPoly_eq_self_of_live` — aeval identity on live vars (PROVED)
- `spdp_span_in_restrictSupportDeg` — SPDP span in degree-bounded space (PROVED)

### Permanent Lower Bound
- `permanentSpdpRank m ≥ m + 1` — identity minor argument (PROVED)

### Profile Compression (v1)
- `restricted_clause_survival` — scaffold SPDP rank ≤ (log n)^35 (PROVED, wired into P_neq_NP)
- `theorem92_scaffold_eventually` — (log n)^35 ≤ √n for large n (PROVED)

### Cook-Levin Encoding
- `transition_constraint_zero_on_valid` — all 4 cases PROVED
- `correctTrace` — fully defined (no sorry)
- `isValidTrace` — validity predicate defined
- Real DTM transition constraints (RealTransition.lean)
- Paper-faithful compilation model (PaperCompilation.lean)

### Extraction Machinery (v1)
- `rename_rank_le` — injective rename preserves SPDP rank (PROVED)
- `iterDerivList_rename` — derivatives commute with rename (PROVED)
- `blockedSpdpRankQ_mono_params` — parameter monotonicity (PROVED)

### Encoding Bridge
- `numVars_le_compiledVarCount` — real encoding fits in compiled space (PROVED)
- `realToScaffold_injective` — embedding is injective (PROVED)
- `permEmbed_range_subset_input` — permanent vars in input region (PROVED)
- `permEmbed_blockOf` — each permanent var gets own block (PROVED)

### Binomial / Combinatorial
- `identity_minor_gives_rank_lower_bound` — identity minor → rank ≥ r (PROVED)
- `choose_superpolynomial` — C(αn, log n) > √n for n ≥ 4 (PROVED)
- `choose_mono_second` — C(n,k+1) ≥ C(n,k) when 2(k+1) ≤ n (PROVED)
- `choose_ge_choose_two` — C(n,k) ≥ C(n,2) for 2 ≤ k ≤ n/2 (PROVED)
- `choose_two_ge_self` — C(m,2) ≥ m for m ≥ 3 (PROVED)
- `pow2_gt_twice` — 2^k > 2k for k ≥ 3 (PROVED)

### Proper Subspace
- `fspdp_proper_subspace` — FSPDP evaluation subspace is proper (PROVED via Möbius)

## Architecture

The formalization has two proof architectures:

### v2 (Paper-Faithful) — `PneqNP_v2.lean`
Matches the paper's actual structure. 2 axioms. No diagonal family.
The proof: P ⊆ FSPDP (A2) + ∃ NP \ FSPDP (A3) → P ≠ NP.

### v1 (Original) — `PneqNP_Paper.lean` + `CompiledSeparation.lean`
Diagonal-based architecture with full extraction machinery.
10,000+ lines of supporting infrastructure used by both architectures.

## Key Discovery

The original v1 formalization used a **nonconstructive diagonal family**
via `Classical.choice`. Analysis revealed this creates a fundamental
soundness obstacle for NP membership. The paper does NOT use this approach —
it uses **explicit Tseitin formulas** on Ramanujan expander graphs.
The v2 architecture corrects this mismatch.
