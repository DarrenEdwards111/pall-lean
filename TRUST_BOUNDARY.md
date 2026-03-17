# Trust Boundary — Compiled-Route Architecture

**Branch:** `compiled-route`
**Build:** 3113 jobs, 0 errors, 0 sorry
**Standard axioms:** propext, Classical.choice, Quot.sound

---

## Theorem Chain

```
P_neq_NP : ¬ P_eq_NP                              [THEOREM]
├── hard_family_in_NP                               [THEOREM]
│   ├── hardNPVerifier                              [structural witness]
│   └── hardNPWitnessBound                          [structural witness]
├── pside_compiled_collapse                         [AXIOM 1]
└── rank_monotone_reduction                         [THEOREM]
    └── compiled_rank_preservation                  [THEOREM]
        ├── permanent_spdp_lower                    [AXIOM 2]
        └── compiled_rank_monotone                  [THEOREM]
            ├── spdp_rank_eval_le                   [AXIOM 3]
            └── perm_restriction_exists             [AXIOM 4]
```

---

## Load-Bearing Axioms (4)

### Axiom 1: `pside_compiled_collapse` — Theorem 92

P-time DTMs produce compiled polynomials with low blocked SPDP rank.

**Paper:** §9 (Width⇒Rank), §17.1 (TM→Polynomial), §17.3 (Global Upper Bound).
**Difficulty:** Highest. Cook-Levin + profile compression + global assembly.
**Attack order:** Last.

### Axiom 2: `permanent_spdp_lower` — Theorem 94

The permanent polynomial perm_m has blocked SPDP rank > m under any partition.

**Paper:** Theorem 94 (exponential SPDP lower bound).
**Difficulty:** High. Pure algebraic lower bound on permanent's structure.
**Attack order:** Third.

### Axiom 3: `spdp_rank_eval_le` — Pure Algebra

Evaluating (specializing) variables in a polynomial can only decrease blocked SPDP rank.

**Paper:** Implicit in Theorem 207's rank-monotone reduction.
**Difficulty:** Medium. Requires coefficient-matrix linear algebra. The analogous statement for arbitrary linear operators is FALSE (counterexample exists); the proof must use polynomial-specific structure (derivative-eval commutativity, evaluated derivatives = 0).
**Attack order:** Second.

### Axiom 4: `perm_restriction_exists` — Structural Embedding

The permanent polynomial can be recovered from any compiled polynomial (of a DTM deciding the hard NP family) by evaluating auxiliary variables. The SPDP rank of the recovered polynomial ≥ the permanent's SPDP rank.

**Paper:** Theorem 207 (rank-monotone block-local reduction).
**Difficulty:** Medium. Concrete construction of the evaluation map.
**Attack order:** First (next target).

---

## Structural Witnesses (2)

### `hardNPVerifier` — DTM

The verifier DTM for the hard NP family. Produced by Theorem 207's reduction.

### `hardNPWitnessBound` — ℕ

Witness length exponent for the hard NP family.

---

## Proved Theorems (5)

| Theorem | From | Content |
|---------|------|---------|
| `hard_family_in_NP` | structural | NP membership from verifier definition |
| `compiled_rank_monotone` | Axioms 3+4 | Compilation preserves permanent's rank |
| `compiled_rank_preservation` | Axioms 2+3+4 | Compiled perm rank > √n (Nat.sqrt arithmetic) |
| `rank_monotone_reduction` | above | ¬CompiledLowRank for any deciding DTM |
| `P_neq_NP` | Axioms 1+2+3+4 | Final separation |

---

## Files

| File | Role |
|------|------|
| `PallLean/CompiledPoly.lean` | Cook-Levin CNF, compiled polynomial, blocked SPDP rank |
| `PallLean/Permanent.lean` | Permanent polynomial (permPoly, permPolyFlat) |
| `PallLean/SPDPMonotone.lean` | SPDP rank monotonicity (eval, embedding) |
| `PallLean/SPDPDefs.lean` | SPDP definitions (partitions, derivatives, subspaces) |
| `PallLean/CompiledSeparation.lean` | All axioms, derived theorems, P_neq_NP |
| `PallLean/TuringMachine.lean` | DTM definition, decides/accepts predicates |

## Attack Order

1. **perm_restriction_exists** — concrete embedding, smallest structural axiom
2. **spdp_rank_eval_le** — pure algebra, needs coefficient-matrix infrastructure
3. **permanent_spdp_lower** — algebraic lower bound
4. **pside_compiled_collapse** — the monster (last)
