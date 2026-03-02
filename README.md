# pall-lean

Lean 4 formalization of "A Compiled SPDP Rank Separation for P ≠ NP" (Edwards, 2025).

## Structure

| File | Paper Section | Status |
|------|--------------|--------|
| `SPDPDefs.lean` | §2 — SPDP Matrix Framework | Axiomatised |
| `Compiler.lean` | §3, 6, 14 — Compilation Model + P-side collapse | Axiomatised |
| `NPWitness.lean` | §7-10 — Ramanujan-Tseitin identity minor | Axiomatised |
| `Extraction.lean` | §11-13 — Extraction map T_Φ | Axiomatised + 1 theorem |
| `Separation.lean` | §15, 19 — Main separation P ≠ NP | 1 sorry (final wiring) |
| `Barriers.lean` | §22, App A — Barrier immunity (non-load-bearing) | Trivial |

## Axiom Inventory

All load-bearing mathematical content is currently axiomatised. The roadmap:

### Phase 1: Core definitions (replace axioms with defs)
- [ ] `SPDPRank` — define as matrix rank of explicit SPDP matrix
- [ ] `BlockPartition` — flesh out with computable block assignment
- [ ] `compiled_polynomial` — construct from TM tableau

### Phase 2: P-side proofs (replace axioms with theorems)
- [ ] `profile_compression` (Lemma 5.7)
- [ ] `within_profile_dim` (Lemma 5.11)
- [ ] `width_to_rank` (Theorem 5.16)
- [ ] `p_side_collapse` (Theorem 6.1)

### Phase 3: NP-side proofs (replace axioms with theorems)
- [ ] `ramanujan_exists` (LPS construction)
- [ ] `disjoint_subfamily` (expander + matching)
- [ ] `np_side_lower_bound` (Theorem 10.1)

### Phase 4: Extraction (the critical joint)
- [ ] `extraction_rank_safe` (Lemma 13.14) — **highest priority**
- [ ] `extraction_correct` (Lemma 13.17)
- [ ] Wire `separation` theorem (remove sorry)

## Building

```bash
lake update
lake build
```

Requires Lean 4.28.0 and mathlib.

## Author

D. J. Edwards, Swansea University
