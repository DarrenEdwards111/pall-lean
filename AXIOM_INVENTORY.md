# Axiom Inventory

## ON-CHAIN (used by P_neq_NP)

1. **cookLevin_rank_bound** (CompiledSeparation.lean:298)
   - Cook-Levin embedding: renamed permanent rank ≤ violation poly rank
   - Paper §11-13

2. **restricted_clause_survival** (CookLevin.lean:1285)
   - P-side: violation poly SPDP rank ≤ (log n)^c
   - Paper §4-5
   - PROVED in ProfileCompression.lean (restricted_clause_survival_from_ml)
   - Proof uses 2 private computation axioms (below)

3. **f_n_family_in_NP** (PneqNP_Paper.lean:144)
   - Diagonal family is in NP
   - Paper §8.6

## OFF-CHAIN (not used by P_neq_NP)

4. **ptime_spdp_collapse** (BoolCircuit.lean:72) — legacy, unused
5. **ambientThresholds_exists** (CookLevin.lean:1086) — legacy, unused by P_neq_NP
6. **cookLevin_extraction** (ExtractionDecomposition.lean:189) — placeholder, unused
7. **profile_count_polylog** (PSideDecomposition.lean:107) — placeholder, unused
8. **per_profile_dim_polylog** (PSideDecomposition.lean:112) — placeholder, unused

## COMPUTATION AXIOMS (used by restricted_clause_survival proof)

9. **scaffold_blockClosure_card_le** (ProfileCompression.lean:156, private)
   - blockClosure of V_ml vars ≤ 24 for scaffold encoding
   - Pure computation, no mathematical content

10. **finrank_restrictSupportDeg_le_axiom** (SupportedDim.lean:138, private)
    - dim(bounded polynomial space) ≤ (|s|+d)^|s|
    - Stars-and-bars counting, no mathematical content
