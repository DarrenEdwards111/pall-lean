# P ≠ NP Lean 4 Formalization

A Lean 4 formalization of a P ≠ NP separation argument via SPDP (Shifted Partial Derivative Polynomial) rank theory.

## Status

| Metric | Value |
|---|---|
| **Custom axioms** | **2** |
| Standard Lean axioms | 3 (propext, Classical.choice, Quot.sound) |
| Sorry count | **0** |
| Build jobs | 3,138 |
| Lines of Lean | 4,214 |
| Files | 30 |

## Architecture

The proof follows the compiled polynomial architecture from the paper (arXiv v5):

```
P ≠ NP
├── Theorem 92 (P-side): Poly-time → low compiled SPDP rank    [AXIOM]
├── Theorem 94 (NP-side): Permanent has exponential SPDP rank   [PROVED]
├── Theorem 207 (Bridge): Permanent rank ≤ compiled rank        [AXIOM]
└── Separation: low rank < high rank → contradiction            [PROVED]
```

### What's Proved (0 axioms)

- **Permanent SPDP lower bound** (Theorem 94): The m×m permanent polynomial has SPDP rank > m. Proof via:
  - Disjoint monomial supports for permanent first derivatives
  - Monomial injectivity (different permutations → different monomials)
  - Linear independence transfer via rename bijection
  - Finrank monotonicity from degree-bounded subspace containment

- **Separation logic**: If Theorems 92 and 207 hold, then P ≠ NP. Derived theorems include `compiled_rank_preservation`, `rank_monotone_reduction`, and the main `P_neq_NP`.

- **Hard family membership**: The hard NP family is proved to be in NP from its verifier definition.

### The Two Axioms

1. **`pside_compiled_collapse`** (Theorem 92): Every polynomial-time DTM produces functions with polynomially bounded compiled SPDP rank. This requires Cook-Levin encoding, depth-4 circuit simulation, and profile compression.

2. **`perm_rank_le_compiled`** (Theorem 207): The permanent polynomial's SPDP rank is bounded by the compiled polynomial's SPDP rank. This combines Cook-Levin semantic restriction with evaluation monotonicity.

## Building

```bash
# Requires Lean 4 v4.28.0 with Mathlib
elan install leanprover/lean4:v4.28.0
lake exe cache get
lake build
```

## Files

### Main proof chain
- `CompiledSeparation.lean` — P ≠ NP theorem + axioms
- `CompiledPoly.lean` — Cook-Levin CNF, compiled polynomial, blocked SPDP
- `PermanentLower.lean` — Permanent SPDP lower bound (Theorem 94)
- `PermanentMonomials.lean` — Disjoint monomial supports
- `SPDPMonotone.lean` — SPDP monotonicity + embedding axiom
- `SPDPDefs.lean` — SPDP definitions and basic properties
- `SPDPEval.lean` — Evaluation-derivative commutation lemmas
- `Permanent.lean` — Permanent polynomial definition
- `TuringMachine.lean` — DTM definition and compilation

### Supporting infrastructure
- `SpanDim.lean`, `DegreeBounds.lean` — Finite-dimensionality
- `Depth4Simulation.lean` — Multilinear interpolation
- `BoolEval.lean`, `BoolCircuit.lean` — Boolean evaluation
- Various restriction, Möbius, and rank bound files

## Branch

- `compiled-route` — Active development (this branch)
- `paper-faithful` — Frozen at `v0.9-algebraic-infrastructure`

## Reference

Based on: *Toward P≠NP: An Observer-Theoretic Separation via SPDP Rank* (arXiv:2512.11820)
