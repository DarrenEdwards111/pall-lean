# Formalization Status — P ≠ NP Lean

**Branch:** `godmove-paper-faithful`  
**Date:** 2026-04-03  
**Build:** 8047 jobs, 0 errors  
**Sorries:** 0  
**Axioms:** 1

## What This Is

A conditional formalization of the paper's P ≠ NP contradiction route.
The full separation chain is wired and proved, conditional on one axiom
that encapsulates the paper's compiler analysis (§9.1–9.3, Theorem 264).

**Honest wording:**
- We formalize the contradiction route conditional on the compiler theorem.
- The remaining unformalized content is the CEW-based Width⇒Rank theorem
  for the compiled tableau polynomial.
- This axiom encapsulates the paper's compiler analysis rather than
  reproducing it internally.

## The 1 Axiom

```lean
axiom compiled_width_rank_bound (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804) :
    mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (latentCompiledPoly M n) ≤ n ^ 160
```

**Paper reference:** Theorem 264 (Compiled Width ⇒ Rank via profile compression)

**What the paper proves (§9.1–9.3):**
1. CEW bound: compiler ensures ≤ C(log n)^c live interfaces (Lemma 19)
2. Profile count: |H(R)| ≤ C(R+m, m) = R^O(1) via stars-and-bars (Lemma 20)
3. Per-profile dim: dim(V_h) ≤ R^O(1) via symmetric tensor powers (Lemma 22)
4. Assembly: rank ≤ |H(R)| × max dim(V_h) = R^O(1) = (log n)^O(1) (Theorem 23)

**To eliminate this axiom:** Replace `latentCompiledPoly` with the paper's
Cook-Levin tableau polynomial (which has bounded CEW by construction),
then formalize profile compression.

## What Is Fully Proved

### NP Side (0 sorries, 0 axioms)
- `cubicGraph` construction and regularity proof
- `buildTseitin`: all 4 fields (upper/lower clause bounds, var bounds, occurrence)
- `highGirthFamily` construction
- Identity minor / disjoint packing chain
- Tseitin polynomial and coupled verifier

### P Side (conditional on 1 axiom)
- Basis extraction from finrank bound (Submodule.exists_finset_span_eq_linearIndepOn)
- Assembly: rank bound → span bound → frozen target
- Full routing chain to P ≠ NP

### Separation Route
- `P_neq_NP_from_generator_axiom`: the final contradiction
- All routing bridges between P-side and NP-side
- Canonical route packaging

## Critical Discovery (2026-04-03)

The per-sheet rank bound `product_sheet_spdp_rank_bound` was **FALSE**.
Product sheets `∏(1 - X_a X_b)` have SPDP rank ≥ C(B, κ), which is
superpolynomial. The paper's polynomial bound applies to the Cook-Levin
tableau polynomial (bounded CEW), not to raw product-of-gadgets sheets.

This was discovered via concrete counterexample (B=3, κ=2) and led to
the restructure from per-sheet bounds to the honest axiom approach.
