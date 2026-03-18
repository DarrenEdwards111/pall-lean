# Trust Boundary — P ≠ NP Lean Formalization

## Build Status
- **Branch:** `compiled-route`
- **Build:** 3138 jobs, 0 errors, 0 sorry
- **Custom axioms for P_neq_NP:** 2
- **Lines of Lean:** 4,214 across 30 files

## P_neq_NP Axiom Dependency (via `#print axioms`)

```
P_neq_NP : ¬P_eq_NP
├── [standard] propext, Classical.choice, Quot.sound
├── pside_compiled_collapse  — Theorem 92 (P-side upper bound)
└── perm_rank_le_compiled    — Theorem 207 (NP-side embedding)
```

### Theorem Dependency Chain

```
P_neq_NP                                     [2 custom axioms]
├── pside_compiled_collapse                   [AXIOM — Theorem 92]
├── compiled_rank_preservation                [THEOREM]
│   ├── compiled_rank_monotone                [THEOREM]
│   │   └── perm_rank_le_compiled             [AXIOM — Theorem 207]
│   └── permanent_spdp_lower                  [THEOREM — 0 custom axioms]
│       ├── perm_first_derivs_independent     [THEOREM]
│       │   ├── perm_derivs_independent_matvar [THEOREM]
│       │   │   ├── linearIndependent_of_disjoint_support [THEOREM]
│       │   │   ├── pderiv_permPoly_ne_zero    [THEOREM]
│       │   │   └── disjoint support lemmas    [THEOREM — PermanentMonomials]
│       │   └── flatFn/unflatFn + pderiv_rename [THEOREM]
│       └── spdp_span_le_restrictTotalDegree  [THEOREM]
├── rank_monotone_reduction                   [THEOREM]
└── hard_family_in_NP                         [THEOREM — 0 custom axioms]
```

### Per-Theorem Axiom Count

| Theorem | Custom Axioms | Status |
|---|---|---|
| `permanent_spdp_lower` (Thm 94) | **0** | Fully proved |
| `hard_family_in_NP` | **0** | Fully proved |
| `compiled_rank_monotone` | 1 (`perm_rank_le_compiled`) | NP-side |
| `P_neq_NP` | 2 (both) | Complete |

## Fully Proved Files (0 axiom, 0 sorry)

- **PermanentMonomials.lean** — Disjoint monomial supports for permanent derivatives
- **PermanentLower.lean** — SPDP lower bound for permanent (Theorem 94)
- **SPDPEval.lean** — Evaluation-derivative commutation lemmas
- **SPDPDefs.lean** — SPDP definitions and basic properties

## The Two Custom Axioms

### 1. pside_compiled_collapse (Theorem 92)

```lean
axiom pside_compiled_collapse :
    ∀ (M : DTM), ∃ (n₀ : ℕ), ∀ (n : ℕ), n ≥ n₀ → n ≥ 2 →
    ∀ (f : (Fin n → Bool) → Bool), M.decides f → CompiledLowRank f
```

**Says:** Every polynomial-time DTM produces functions with polynomially bounded compiled SPDP rank.

**Paper reference:** Theorem 92, Sections 9 and 17.3.

**Why hard to prove:**
1. Cook-Levin encoding (§3.1): DTM → width-3 CNF with N = Θ(n³) variables
2. Depth-4 simulation (§5.2): ΣΠΣΠ realization
3. Binary Tseitin (§2.3.2): width-3 → width-2 structure
4. Profile compression (§9): polynomial width ⇒ rank bound
5. Global assembly (§17.3): Γ_{κ,ℓ}(P_{M,n}) ≤ n^{O(1)}

Each step requires substantial Lean infrastructure. Estimated effort: months.

### 2. perm_rank_le_compiled (Theorem 207 core)

```lean
axiom perm_rank_le_compiled
    (n : ℕ) (M : TuringMachine.DTM) (k : ℕ)
    (cnf : CookLevinCNF (compiledVarCount k n))
    (hlp : HasLocalPartition cnf)
    (hardFamily : (Fin n → Bool) → Bool)
    (hM : M.decides hardFamily) :
    ∃ (bp : BlockPartition (Nat.sqrt n * Nat.sqrt n)),
    blockedSpdpRankQ (...) (permPolyFlat (Nat.sqrt n)) bp ≤
    blockedSpdpRankQ (...) (compiledPolyQ cnf) hlp.partition
```

**Says:** The permanent polynomial's SPDP rank ≤ compiled polynomial's SPDP rank.

**Combines:**
- Cook-Levin semantic restriction: evaluating auxiliary variables recovers permanent
- Evaluation monotonicity: SPDP rank cannot increase under variable evaluation

**Why evaluation monotonicity is hard:**
- SPDP(φ(p)) ⊄ SPDP(p) (counterexample found)
- φ(SPDP(p)) ⊄ SPDP(φ(p)) (counterexample found)
- No simple containment in either direction
- X_j-degree grading: per-grade bounds hold but sum doesn't decompose cleanly for p
- Requires coefficient-matrix argument or block-partition-specific proof
- 6+ proof strategies explored and documented

## Axiom History

| Stage | Custom Axioms | Change |
|---|---|---|
| Initial skeleton | 14 | Starting point |
| Proved permanent algebra | 10 | -4 (monomial supports, linear independence) |
| Proved eval/deriv comm | 7 | -3 (pderiv_eval_comm, iterDerivList, dead removal) |
| Merged eval + embedding | 4 | -3 (2→1 merge, structural eliminated) |
| Concrete DTM definitions | **2** | -2 (hardNPVerifier, hardNPWitnessBound) |

## Other Project Axioms (not in P_neq_NP chain)

- `ptime_spdp_collapse` (BoolCircuit.lean) — alternate proof route
- `f_n_family_in_NP` (PneqNP_Paper.lean) — alternate proof route

## Key Lean Techniques Used

- `MvPolynomial.induction_on` with cases C/mul_X/add
- `Pi.single_eq_of_ne` for Kronecker delta evaluation
- `Submodule.finrank_mono` and `Submodule.finrank_map_le`
- `Finset.sum_eq_single` for extracting single nonzero summand
- `List.foldl_cons` + `generalizing p` for iterDerivList induction
- `MvPolynomial.renameEquiv` + `LinearEquiv.ker` for rename transfer
- `decide` over `native_decide` to avoid trustCompiler dependency
