# P ≠ NP Lean 4 Formalization

A Lean 4 formalization of a P ≠ NP separation argument via SPDP (Shifted Partial Derivative Polynomial) rank theory, following [arXiv:2512.11820v5](https://arxiv.org/abs/2512.11820v5) (Edwards, 2025).

## Results

```
P_neq_NP : ¬P_eq_NP
├── [standard]  propext, Classical.choice, Quot.sound
├── [axiom]     pside_compiled_collapse    — Paper Theorem 92
└── [axiom]     cook_levin_perm_embed      — Paper Lemma 206
```

| Metric | Value |
|---|---|
| Custom axioms for `P_neq_NP` | **2** |
| Standard Lean axioms | 3 |
| Sorry count | **0** |
| Build jobs | 3,138 |
| Lines of Lean | 4,480 |
| Files | 31 |

## What's Proved (0 custom axioms)

- **Theorem 94** — Permanent has exponential SPDP rank: Γ_{κ,0}(perm_n) ≥ C(n,κ)
  - Lemma 95 — Disjoint-witness independence (different derivatives → disjoint monomial supports)
  - Monomial injectivity (different permutations produce different monomials)
  - Linear independence transfer via rename bijection from MatVar to Fin(m²)
- **Lemma 33** — Restriction monotonicity: SPDP rank cannot increase under variable evaluation
  - `pderiv_evalOne_self` — Derivative at evaluated variable = 0
  - `iterDerivList_evalOne_zero_no_nodup` — Iterated derivative containing evaluated var = 0
  - `freeSpdp_evalOne_le` — Free-variable SPDP of φ(p) ⊆ φ-image of SPDP(p)
- **Theorem 92** — P-side upper bound (derived from axiom `pside_compiled_collapse`)
- **Theorem 147/207** — P ≠ NP separation (derived from both axioms)
- **Hard family membership** — hardNPFamily ∈ NP (from concrete verifier definition)

## The Two Axioms

### Axiom 1: `pside_compiled_collapse` (Paper Theorem 92)

> Every polynomial-time DTM produces functions with compiled SPDP rank ≤ √n.

Combines Cook-Levin construction (§17.1), profile compression (§8/§17.3), and asymptotic comparison ((log n)^C ≤ √n).

### Axiom 2: `cook_levin_perm_embed` (Paper Lemma 206)

> The permanent polynomial's SPDP rank is bounded by the compiled polynomial's SPDP rank.

The extraction map (restriction + projection) is rank-monotone by Lemma 33 (proved) and Lemma 34 (submatrix monotonicity). The remaining content: Cook-Levin encoding preserves permanent algebraic structure.

## Architecture

```
CompiledSeparation.lean ← Main theorem + axioms
├── PermanentLower.lean  ← Theorem 94 (PROVED, 0 axioms)
│   └── PermanentMonomials.lean  ← Lemma 95 (PROVED)
├── SPDPMonotone.lean    ← Lemma 206 axiom
│   └── SPDPRestrict.lean  ← Lemma 33 (PROVED)
│       └── SPDPEval.lean  ← Evaluation lemmas (PROVED)
│           └── CoeffMatrix.lean  ← Derivative subspace (PROVED)
├── CompiledPoly.lean    ← Cook-Levin CNF, compiled polynomial
├── Permanent.lean       ← Permanent polynomial
├── SPDPDefs.lean        ← SPDP definitions
└── TuringMachine.lean   ← DTM definitions
```

## Building

```bash
elan install leanprover/lean4:v4.28.0
cd pall-lean
lake exe cache get
lake build
```

## Verification

```bash
# Check axiom dependencies
echo 'import PallLean.CompiledSeparation
#print axioms CompiledSeparation.P_neq_NP' > check.lean
lake env lean check.lean
```

## Branch

- `compiled-route` — Active development
- `paper-faithful` — Frozen at `v0.9-algebraic-infrastructure`

## Paper

Based on: *Toward P≠NP: An Observer-Theoretic Separation via SPDP Rank and a ZFC-Equivalent Foundation within the N-Frame Model* ([arXiv:2512.11820v5](https://arxiv.org/abs/2512.11820v5))

SPDP toolkit: [arXiv:2512.20729](https://arxiv.org/abs/2512.20729)
