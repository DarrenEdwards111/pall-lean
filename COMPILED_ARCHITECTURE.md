# Compiled-Route Architecture — P ≠ NP via P_{M,n}

## Core Object

The **compiled polynomial** P_{M,n} ∈ F_p[x₁,...,x_N], where:
- M is a deterministic Turing machine
- N = Θ(n³) variables from Cook-Levin encoding
- Each variable represents a cell of the computation tableau
- The polynomial has **block-locality**: each gate/clause touches O(1) variables
- Field: F_p with safe prime p_n > n^20

This replaces `multilinearInterp(f)` from the algebraic-infrastructure branch.

## Paper's Spine (arXiv v5)

### Theorem 92 — P-side Upper Bound
Every P-time TM M has:
  Γ_{κ,ℓ}(P_{M,n}) ≤ poly(n)  at  κ = ℓ = Θ(log n)

Proof route: Cook-Levin → block-local polynomial → profile compression (Section 9)
→ global assembly (Section 17.3)

### Theorem 94 — NP-side Lower Bound
The diagonal family's compiled polynomial has:
  Γ_{κ,ℓ}(P_{diag,n}) ≥ n^{Ω(log n)}  (superpolynomial)

### Section 11.7 — Constructive Witness
Deterministic, polynomial-time construction of w ∈ V_n^⊥.
This replaces our Classical.choice-based dualAnnihilator.
Makes f_n ∈ NP provable without non-constructive existence.

### Theorem 207 — Main Separation
P ≠ NP, combining Theorems 92 + 94 + constructive witness.

## Dependency Chain

```
Cook-Levin encoding
    │
    ▼
Compiled polynomial P_{M,n}  ←── block-local structure
    │
    ├──► P-side (Thm 92): profile compression → Γ ≤ poly(n)
    │
    ├──► NP-side (Thm 94): lower bound → Γ ≥ n^{Ω(log n)}
    │
    ├──► Constructive witness (§11.7): w ∈ V_n^⊥ in poly-time
    │
    └──► Separation (Thm 207): P ≠ NP
```

## New Lean Files (Planned)

### Layer 1: Cook-Levin Infrastructure
- `CompiledPoly.lean` — Define P_{M,n}: DTM → polynomial via Cook-Levin
  - Computation tableau as variables
  - Clause polynomials from transition function
  - Block partition from locality structure
  - Key property: each clause touches O(1) variables

### Layer 2: SPDP on Compiled Polynomials
- `CompiledSPDP.lean` — SPDP rank of P_{M,n}
  - Definition 12: blocked SPDP matrix M^B_{κ,ℓ}(P_{M,n})
  - Block-admissible basis
  - Profile types (Section 9)

### Layer 3: P-side Upper Bound
- `ProfileCompression.lean` — Section 9: Width ⇒ Rank via profiles
  - Constant-type profiles
  - Per-profile rank bound
  - Profile counting
- `PsideUpperBound.lean` — Section 17.3: Global bound Γ ≤ poly(n)

### Layer 4: NP-side Lower Bound
- `NpsideLowerBound.lean` — Theorem 94
  - Diagonal family definition (constructive, not Choice-based)
  - Lower bound on compiled SPDP rank

### Layer 5: Constructive Witness & Separation
- `ConstructiveWitness.lean` — Section 11.7: w ∈ V_n^⊥ in poly-time
- `Separation.lean` — Theorem 207: P ≠ NP

## Reusable from algebraic-infrastructure branch

The following are target-independent and can be imported:
- `MobiusInversion.lean` — toggle involution, superset sum lemmas
- `DegreeBounds.lean` — totalDegree_pderiv_le, totalDegree_iterDerivList_le
- `SPDPDefs.lean` — basic SPDP definitions (spdpSubspace, iterDerivList)
- `TuringMachine.lean` — DTM definition
- `BoolEval.lean` — boolToRat, evalVec basics

The following are multilinearInterp-specific and stay on the old branch:
- MobiusBridge, MobiusTopCoeff, ProperSubspaceGeneral
- RankLowerBound, MultilinearRestrict, RestrictIndicator
- IterDerivTopCoeff, SpanDim, TopCoeffExtract
- PneqNP_Paper, PneqNP_Defs (need rewrite for compiled objects)

## Key Differences from Old Architecture

| Aspect | Old (multilinearInterp) | New (compiled P_{M,n}) |
|--------|------------------------|----------------------|
| Target polynomial | Truth table interpolation | Cook-Levin encoding |
| Variables | n (input bits) | N = Θ(n³) (tableau) |
| Locality | None | O(1) per clause |
| P-side mechanism | Decision tree depth | Profile compression |
| NP-side mechanism | Möbius top coefficient | Compiled lower bound |
| Escape mechanism | Dual annihilator (Choice) | Constructive w ∈ V_n^⊥ |
| Parameter regime | κ = ℓ = w (inconsistent) | κ = ℓ = Θ(log n), κ < w |
| Field | ℚ | F_p (safe prime) |

## First Milestone

Define `CompiledPoly` with the block-locality property and state
the P-side axiom (Theorem 92) in terms of it. Verify that the parity
counterexample does NOT apply to the compiled object.
