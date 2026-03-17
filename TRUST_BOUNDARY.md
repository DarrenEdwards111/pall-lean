# Trust Boundary — P ≠ NP Lean Formalization

## Build Status
- **Branch:** `compiled-route`
- **Build:** 3138 jobs, 0 errors, 0 sorry
- **Custom axioms for P_neq_NP:** 4 (2 structural + 2 load-bearing)

## P_neq_NP Axiom Dependency (via `#print axioms`)

```
P_neq_NP : ¬P_eq_NP
├── [standard] propext, Classical.choice, Quot.sound
├── [structural] hardNPVerifier : DTM
├── [structural] hardNPWitnessBound : ℕ
├── [load-bearing] pside_compiled_collapse  — Theorem 92 (P-side upper bound)
└── [load-bearing] perm_rank_le_compiled    — Theorem 207 (NP-side embedding)
```

### Proof Chain

```
P_neq_NP
├── pside_compiled_collapse          [AXIOM — Theorem 92, §9/§17.3]
├── compiled_rank_preservation       [THEOREM]
│   ├── compiled_rank_monotone       [THEOREM]
│   │   └── perm_rank_le_compiled    [AXIOM — Theorem 207 core]
│   └── permanent_spdp_lower         [THEOREM — fully proved, 0 axioms]
│       ├── perm_first_derivs_independent  [THEOREM]
│       │   ├── perm_derivs_independent_matvar  [THEOREM]
│       │   │   ├── linearIndependent_of_disjoint_support  [THEOREM]
│       │   │   ├── pderiv_permPoly_ne_zero  [THEOREM]
│       │   │   └── pderiv_permPoly_disjoint_diff_row/col  [THEOREM]
│       │   └── flatFn/unflatFn bijection + pderiv_rename  [THEOREM]
│       └── spdp_span_le_restrictTotalDegree  [THEOREM]
├── rank_monotone_reduction          [THEOREM]
└── hard_family_in_NP                [THEOREM]
```

## Fully Proved Files (0 axiom, 0 sorry)

- **PermanentMonomials.lean**: Disjoint monomial supports for permanent derivatives
- **PermanentLower.lean**: SPDP lower bound for permanent (Theorem 94)
- **SPDPEval.lean**: pderiv_evalOne_self, iterDerivList_evalOne_comm/zero

## Load-Bearing Axioms

### 1. pside_compiled_collapse (Theorem 92)
**Statement:** For any poly-time DTM M, the compiled polynomial's blocked SPDP rank is polynomially bounded.
**Paper reference:** Theorem 92, Sections 9 and 17.3
**Difficulty:** Extreme. Requires Cook-Levin formalization, depth-4 circuit simulation, binary Tseitin encoding, profile compression. Multi-year effort.
**Status:** Kept as axiom.

### 2. perm_rank_le_compiled (Theorem 207 core)
**Statement:** The permanent polynomial's SPDP rank ≤ the compiled polynomial's SPDP rank.
**Paper reference:** Theorem 207 + evaluation monotonicity
**What it combines:**
  - Cook-Levin semantic restriction: evaluating auxiliary variables recovers permanent structure
  - Evaluation monotonicity: SPDP rank cannot increase under variable evaluation
**Difficulty:** High. Needs Cook-Levin encoding structure + evaluation monotonicity proof.
**Status:** Kept as axiom. Previously was two separate axioms (spdp_rank_eval_le + perm_restriction_exists), merged for cleaner trust boundary.

## Structural Axioms

### hardNPVerifier : DTM
Asserts the existence of a DTM that verifies witnesses for the hard NP family.
Any NP-complete verifier (e.g., SAT checker) would work.
Could be eliminated by defining a concrete verifier, but this is standard CS
infrastructure, not mathematically interesting.

### hardNPWitnessBound : ℕ
The polynomial witness bound exponent.
Could be eliminated with a concrete value (e.g., 1 for SAT).

## Other Project Axioms (not in P_neq_NP chain)

- `ptime_spdp_collapse` (BoolCircuit.lean) — same as pside_compiled_collapse, used by alternate proof file
- `f_n_family_in_NP` (PneqNP_Paper.lean) — used only by alternate proof

## Axiom History

| Date | Count | Change |
|------|-------|--------|
| Start | 14 | Initial compiled-route skeleton |
| Session 2 | 10 | Proved permanent algebra (4 eliminated) |
| Session 3 | 7 | Proved eval/deriv comm + removed dead (3 eliminated) |
| Session 3 | 4 | Merged eval monotonicity + embedding (2→1) |

## Key Lean API Lessons

- `MvPolynomial.induction_on` cases: `C`, `mul_X`, `add`
- `Pi.single_eq_of_ne` for Kronecker delta = 0
- `pderiv_X` resolves to `Pi.single` (not `if-then-else`)
- `Submodule.finrank_map_le` for linear map dimension bound
- `Submodule.finrank_mono` for submodule dimension bound
- `List.foldl_cons` to unfold iterDerivList
- `generalizing p` needed for list induction on iterDerivList
