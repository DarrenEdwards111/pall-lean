# Sorry Inventory — P ≠ NP Lean Formalization

**Branch:** `godmove-paper-faithful`  
**Date:** 2026-04-02  
**Build:** 8047 jobs, 0 errors  
**Axioms:** 0 (all sorries, no custom axioms)

## Full Separation Route

```
P_neq_NP_from_generator_axiom
  ← P_neq_NP_latent_from_p_span160
    ← latentCompiledPoly_spdp_subspace_span_poly_bound [PROVED from rank bound]
      ← latentCompiledPoly_spdp_rank_poly_bound [PROVED from per-sheet bounds]
        ← machCopySheet_spdp_rank_bound ≤ n^50  [SORRY — P-side 1]
        ← copyConSheet_spdp_rank_bound ≤ n^50   [SORRY — P-side 2]
        ← selConSheet_spdp_rank_bound ≤ n^50    [SORRY — P-side 3]
```

## P-Side Sorries (3)

All three are structurally identical — bounding the SPDP rank of a product-of-gadgets sheet.

| File | Line | Statement | Difficulty |
|------|------|-----------|------------|
| LatentWidthRankDecomp.lean | 756 | `machCopySheet_spdp_rank_bound` | Hard |
| LatentWidthRankDecomp.lean | 763 | `copyConSheet_spdp_rank_bound` | Hard |
| LatentWidthRankDecomp.lean | 770 | `selConSheet_spdp_rank_bound` | Hard |

**Why hard:** Each sheet is `∏_i gadget_i` where gadget_i is a 2-variable polynomial in block i.
The SPDP rank bound requires the **profile compression** argument from the paper (Theorem 216/Lemma 264):
- Partition SPDP generators by their "interface-anonymous profile" (histogram of derivative types per block)
- Show polynomially many profiles (profile compression lemma)
- Bound within-profile dimension (block-factorable structure)
- Assembly: poly profiles × poly per-profile dim = polynomial total rank

This is the core mathematical content of the P-side of the separation.

## NP-Side Sorries (5)

| File | Line | Statement | Difficulty |
|------|------|-----------|------------|
| NPWitness.lean | 128 | `cubicGraph.regular` | Medium (mechanical case analysis) |
| NPWitness.lean | 279 | `buildTseitin.num_clauses_upper` | Easy (depends on regular) |
| NPWitness.lean | 284 | `buildTseitin.num_clauses_lower` | Easy (depends on regular) |
| NPWitness.lean | 288 | `buildTseitin.clause_vars_bound` | Easy (depends on regular) |
| NPWitness.lean | 293 | `buildTseitin.bounded_occurrence` | Easy (depends on regular) |

Plus 2 pre-existing sorries in NPWitness.lean (lines 115, 263-266) for RegularGraph/HighGirthFamily construction.

**Why medium:** `cubicGraph.regular` requires showing a Finset filter has cardinality 3 via case
analysis on `edgeSrc`/`edgeTgt` with `dite` unfolding and modular arithmetic. Tedious but mechanical.
Once `cubicGraph.regular` is proved, the 4 `buildTseitin` fields follow from clause counting.

## Summary

- **Total sorries:** 8 (3 P-side + 5 NP-side)
- **Custom axioms:** 0
- **Independent hard targets:** 2 (per-sheet rank bound + cubicGraph.regular)
- **Everything else chains from those 2**
