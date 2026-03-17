# Trust Boundary — P ≠ NP Lean Formalization

## Build Status
- **Branch:** `compiled-route`
- **Build:** 3138 jobs, 0 errors, 0 sorry
- **Score:** 10 axioms (3 load-bearing complexity + 3 structural + 4 standard)

## P_neq_NP Axiom Dependency Chain

```
P_neq_NP (CompiledSeparation.lean)
├── pside_compiled_collapse          [AXIOM — Theorem 92, P-side]
├── compiled_rank_preservation       [THEOREM]
│   ├── compiled_rank_monotone       [THEOREM]
│   │   ├── spdp_rank_eval_le       [AXIOM — evaluation monotonicity]
│   │   └── perm_restriction_exists  [AXIOM — Cook-Levin embedding]
│   └── permanent_spdp_lower        [THEOREM — fully proved]
│       ├── perm_first_derivs_independent  [THEOREM]
│       │   ├── perm_derivs_independent_matvar  [THEOREM]
│       │   │   ├── linearIndependent_of_disjoint_support  [THEOREM]
│       │   │   ├── pderiv_permPoly_ne_zero  [THEOREM]
│       │   │   │   └── perm_monomials_injective  [THEOREM]
│       │   │   └── pderiv_permPoly_disjoint_diff_row/col  [THEOREM — PermanentMonomials]
│       │   └── pderiv_rename + flatFn/unflatFn bijection  [THEOREM]
│       └── spdp_span_le_restrictTotalDegree  [THEOREM]
├── rank_monotone_reduction          [THEOREM]
├── hard_family_in_NP                [THEOREM]
└── constructive_witness             [AXIOM — §11.7, supporting]
```

## Fully Proved Files (0 axiom, 0 sorry)

- **PermanentMonomials.lean**: Disjoint monomial supports for permanent derivatives
  - Derivation.leibniz_prod, pderiv_permPoly, prod_X_eq_monomial
  - pderiv_permPoly_disjoint_diff_row/col
- **PermanentLower.lean**: SPDP lower bound for permanent (Theorem 94)
  - perm_monomials_injective, pderiv_permPoly_ne_zero
  - perm_derivs_independent_matvar, perm_first_derivs_independent
  - permanent_spdp_lower

## Load-Bearing Axioms (3)

### Axiom 1: `pside_compiled_collapse` — Theorem 92
P-time DTMs produce compiled polynomials with low blocked SPDP rank.
**Paper:** §9 + §17.1 + §17.3. Cook-Levin + profile compression.
**Difficulty:** Highest. Multi-year formalization effort.

### Axiom 2: `spdp_rank_eval_le`
Evaluating variables decreases blocked SPDP rank.
**Paper:** §2 rank monotonicity under specialization.
**Difficulty:** High. Requires showing SPDP span of φ(p) ≤ dim(SPDP span of p).
**Challenge:** Shift monomials in the SPDP of φ(p) can use evaluated variables,
so simple φ-image argument fails. Correct proof needs coefficient-matrix
infrastructure or block-partition analysis.
**6 failed approaches documented (session 2026-03-15):**
1. Direct Submodule.map — doesn't account for shift monomials
2. Finrank_mono — generating sets don't nest
3. Matrix rank — needs column-collapse infrastructure
4. Abstract version is FALSE (finite-dim counterexample)
5. Derivation algebra — doesn't capture block structure
6. Evaluation as projection — blocks don't decompose cleanly

### Axiom 3: `perm_restriction_exists`
Permanent embeds in compiled polynomial via variable evaluation.
**Paper:** Theorem 207 + Cook-Levin encoding.
**Difficulty:** High. Needs Cook-Levin formalization.

## Proved Theorems (supporting axioms eliminated this session)

### `pderiv_eval_comm` — was axiom, now THEOREM
∂_i(p[x_j := c]) = (∂_i p)[x_j := c] for i ≠ j.
Proof: induction on MvPolynomial (C/mul_X/add cases), case split on i = s.

### `iterDerivList_eval_comm` — was axiom, now THEOREM
Iterated derivative commutes with evaluation when variables disjoint.
Proof: list induction + pderiv_eval_comm.

### `pderiv_permPoly_ne_zero` — was axiom, now THEOREM
Each sub-permanent is nonzero.
Proof: different permutations give different monomials (perm_monomials_injective),
so the coefficient of σ₀'s monomial in the sum is exactly 1.

### `perm_first_derivs_independent` — was axiom, now THEOREM
m² derivatives of perm are linearly independent on Fin(m*m).
Proof: transfer from MatVar via flatFn/unflatFn bijection + pderiv_rename.

## Structural Axioms (not on critical path for elimination)

- `cook_levin`: Cook-Levin theorem (standard CS)
- `hardNPVerifier` / `hardNPWitnessBound` / `hardNPWitnessBound_pos`: DTM existence
- `constructive_witness`: §11.7 supporting axiom
- `ptime_spdp_collapse`: Boolean circuit → SPDP (BoolCircuit.lean)
- `f_n_family_in_NP`: NP membership (PneqNP_Paper.lean, alternate file)

## Session History
- **2026-03-17**: Eliminated 4 axioms (14→10). Proved perm_monomials_injective,
  pderiv_permPoly_ne_zero, perm_first_derivs_independent, pderiv_eval_comm,
  iterDerivList_eval_comm. Created PermanentMonomials.lean (0 sorry, 0 axiom).
  PermanentLower.lean now fully proved (0 sorry, 0 axiom).
