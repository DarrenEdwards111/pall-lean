# Trust Boundary — Compiled-Route Architecture

**Branch:** `compiled-route`
**Build:** 3137 jobs, 0 errors, 0 sorry
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
        ├── permanent_spdp_lower                    [THEOREM]
        │   ├── perm_first_derivs_independent       [THEOREM]
        │   │   └── perm_derivs_have_unique_monomials [AXIOM 2]
        │   │       (+ linearIndependent_of_unique_coeff [THEOREM])
        │   ├── spdp_span_le_restrictTotalDegree    [THEOREM]
        │   └── Submodule.finrank_mono              [MATHLIB]
        └── compiled_rank_monotone                  [THEOREM]
            ├── spdp_rank_eval_le                   [AXIOM 3]
            └── perm_restriction_exists             [AXIOM 4]
```

---

## Load-Bearing Axioms (4)

### Axiom 1: `pside_compiled_collapse` — Theorem 92

P-time DTMs produce compiled polynomials with low blocked SPDP rank.

**Paper:** §9 + §17.1 + §17.3.
**Difficulty:** Highest. Cook-Levin + profile compression.

### Axiom 2: `perm_derivs_have_unique_monomials`

Each first derivative of perm_m has a monomial appearing in no other derivative.

**Proof sketch (complete, not yet formalized):**
- ∂_{(i₀,j₀)}(perm) = Σ_{σ: σ(i₀)=j₀} ∏_{i≠i₀} X(i,σ(i))
- Each monomial covers all rows ≠ i₀ and all columns ≠ j₀
- For (i₀',j₀') ≠ (i₀,j₀):
  - i₀' ≠ i₀ ⟹ monomial uses row i₀', but ∂_{(i₀',j₀')} excludes it
  - j₀' ≠ j₀ ⟹ monomial uses col j₀', but ∂_{(i₀,j₀')} excludes it
- Derivative supports are pairwise DISJOINT (stronger than unique monomials)
- Nonzero: identity permutation contributes a term

**Missing Lean infrastructure:** Leibniz rule for `pderiv` on `Finset.prod`
(not in Mathlib). ~100 lines to formalize.

### Axiom 3: `spdp_rank_eval_le`

Evaluating variables decreases blocked SPDP rank.

**Missing:** Coefficient-matrix infrastructure (see failed proof avenues in
previous version of this file).

### Axiom 4: `perm_restriction_exists`

Permanent embeds in compiled polynomial via variable evaluation.

**Missing:** Full Cook-Levin formalization.

---

## Structural Witnesses (2)

- `hardNPVerifier` — DTM
- `hardNPWitnessBound` — ℕ (+ positivity)

---

## Proved Theorems (10)

| Theorem | Content |
|---------|---------|
| `linearIndependent_of_unique_coeff` | Polynomials with unique witness monomials are linearly independent |
| `perm_first_derivs_independent` | m² first derivatives of perm_m are linearly independent |
| `spdp_gen_totalDegree_le` | SPDP generators have bounded degree |
| `spdp_span_le_restrictTotalDegree` | SPDP span ⊆ degree-bounded submodule |
| `permanent_spdp_lower` | SPDP rank of perm_m > m (Theorem 94) |
| `hard_family_in_NP` | NP membership from verifier definition |
| `compiled_rank_monotone` | Compilation preserves permanent's rank |
| `compiled_rank_preservation` | Compiled rank > √n |
| `rank_monotone_reduction` | ¬CompiledLowRank for any deciding DTM |
| `P_neq_NP` | Final separation |

---

## Files

| File | Role |
|------|------|
| `PallLean/PermanentLower.lean` | Permanent lower bound: independence → rank ≥ m² → rank > m |
| `PallLean/CompiledSeparation.lean` | Main theorem chain + P_neq_NP |
| `PallLean/SPDPMonotone.lean` | SPDP rank monotonicity |
| `PallLean/CompiledPoly.lean` | Cook-Levin CNF, compiled polynomial |
| `PallLean/Permanent.lean` | Permanent polynomial definitions |
| `PallLean/SPDPDefs.lean` | SPDP fundamentals |
| `PallLean/TuringMachine.lean` | DTM definition |
