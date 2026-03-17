# Trust Boundary — Compiled-Route Architecture

## Status

P_neq_NP proved from **4 paper-faithful axioms** on the compiled polynomial P_{M,n}.

**Branch:** `compiled-route`  
**Build:** 3111 jobs, 0 errors, 0 sorry  
**Custom axioms:** 4 (each maps to one paper section)  
**Standard axioms:** propext, Classical.choice, Quot.sound  

---

## Axiom 1: `pside_compiled_collapse` — Paper Theorem 92 / §9 / §17.3

Every P-time DTM M produces a compiled Cook-Levin polynomial with blocked SPDP rank ≤ √n at κ = ℓ = log₂ n, for large n.

**Used by:** `ptime_implies_low_rank` → `P_neq_NP`  
**Full proof requires:** Cook-Levin encoding, profile compression, global rank assembly.

## Axiom 2: `constructive_witness` — Paper §11.7

For large n, there exists w ∈ V_n^⊥ (orthogonal to the compiled evaluation subspace) with a positive entry, constructible in deterministic polynomial time.

**Used by:** `getAnnihilator` → `diagonalFamily` → `P_neq_NP`  
**Full proof requires:** Explicit subspace basis computation, linear algebra over F_p.

## Axiom 3: `diagonal_escape` — Paper Theorem 94

The diagonal function (defined via the constructive annihilator) escapes compiled low rank: its compiled SPDP rank exceeds √n for all large n.

**Used by:** `P_neq_NP` (directly)  
**Full proof requires:** NP-side lower bound on compiled polynomial.

## Axiom 4: `diagonal_in_NP` — Paper Theorem 94 (b)

The diagonal family is in NP (polynomial witness + poly-time verifier).

**Used by:** `P_neq_NP` (directly)  
**Full proof requires:** Witness = annihilator w, verifier = orthogonality check.

---

## Dependency Graph

```
pside_compiled_collapse ──► ptime_implies_low_rank (theorem)
                                      │
constructive_witness ──► getAnnihilator ──► diagonalFamily
                                      │
diagonal_escape ──────────────────────┤
diagonal_in_NP ───────────────────────┤
                                      ▼
                                 P_neq_NP (theorem)
```

## Attack Order

1. `diagonal_in_NP` + `constructive_witness` (narrowest, NP-side)
2. `diagonal_escape` (NP-side lower bound)
3. `cook_levin` + `pside_compiled_collapse` (deepest, P-side)

## Key Architectural Decision

The old `paper-faithful` branch (tag `v0.9-algebraic-infrastructure`) measured SPDP rank of `multilinearInterp(f)`. This is the wrong object — parity is P-time but has rank ≥ 2^w at κ = w, creating an inconsistency. The compiled-route branch measures rank of the Cook-Levin polynomial P_{M,n}, which has block-locality that profile compression exploits. See `ARCHITECTURE_MISMATCH.md`.
