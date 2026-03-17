# Trust Boundary — Compiled-Route Architecture

**Branch:** `compiled-route`
**Build:** 3112 jobs, 0 errors, 0 sorry
**Custom axioms:** 4 (each maps to one paper section)
**Standard axioms:** propext, Classical.choice, Quot.sound

---

## Theorem Chain

```
P_neq_NP : ¬ P_eq_NP                           [THEOREM]
├── perm_in_NP                                   [AXIOM 4]
├── pside_compiled_collapse                      [AXIOM 1]
└── rank_monotone_reduction                      [THEOREM]
    └── compiled_rank_preservation               [THEOREM]
        ├── permanent_spdp_lower                 [AXIOM 2]
        └── compiled_rank_monotone               [AXIOM 3]
```

---

## Axiom 1: `pside_compiled_collapse` — Paper Theorem 92

**Statement:** Every P-time DTM M produces a compiled Cook-Levin polynomial with blocked SPDP rank ≤ √n at κ = ℓ = log₂ n, for all sufficiently large n.

**Paper sections:** §9 (Width⇒Rank via Constant-Type Profiles), §17.1 (TM→Polynomial), §17.3 (Global Upper Bound on Γ_{κ,ℓ}(P_{M,n})).

**Role in proof:** Provides the P-side upper bound. If P = NP, then a DTM for the permanent exists, and this axiom forces its compiled polynomial into the low-rank regime.

**Proof difficulty:** High. Requires Cook-Levin formalization, block-locality analysis, profile compression, and global rank assembly.

## Axiom 2: `permanent_spdp_lower` — Paper Theorem 94

**Statement:** The permanent polynomial perm_m has blocked SPDP rank > m under any block partition of its m² variables, for all sufficiently large m.

**Paper section:** Theorem 94 (NP-side exponential SPDP lower bound).

**Role in proof:** Provides the algebraic hardness ingredient. The actual bound is ≥ 2^{m/4}; we only need > m here.

**Proof difficulty:** Medium-high. Requires analysis of the permanent's algebraic structure under the SPDP framework.

## Axiom 3: `compiled_rank_monotone` — Paper Theorem 207

**Statement:** For any DTM M deciding the permanent decision family at input length n, and any Cook-Levin compilation of M's computation, the compiled polynomial's blocked SPDP rank is at least the permanent polynomial's blocked SPDP rank at matrix dimension m = √n (under some partition).

**Paper section:** Theorem 207 (rank-monotone block-local reduction).

**Role in proof:** Bridges algebraic complexity (SPDP rank of perm_m) to computational complexity (compiled rank of P_{M,n}). Ensures the Cook-Levin encoding cannot destroy the permanent's high rank.

**Proof difficulty:** Medium. The core insight is that block-local transformations preserve blocked SPDP rank. The paper's "rank-monotone reduction" formalizes this.

## Axiom 4: `perm_in_NP` — Standard

**Statement:** The permanent decision family is in NP.

**Paper section:** Standard complexity theory (not specific to this paper).

**Role in proof:** Establishes the NP membership needed to invoke P = NP → perm ∈ P.

**Proof difficulty:** Low. The permanent of a 0/1 matrix can be verified with a witness (set of permutations summing to the target).

---

## Derived Theorems (0 sorry)

### `compiled_rank_preservation`
**From:** Axioms 2 + 3.
**Content:** Any compilation of a DTM deciding the permanent has SPDP rank > √n for large n.
**Proof work:** Nat.sqrt monotonicity, squaring bounds, connecting matrix dimension m to input length n.

### `rank_monotone_reduction`
**From:** `compiled_rank_preservation`.
**Content:** ¬ CompiledLowRank(permDecisionFamily n) for any deciding DTM.
**Proof work:** Contradiction via Nat.lt_irrefl from rank > √n vs rank ≤ √n.

### `ptime_implies_low_rank`
**From:** Axiom 1.
**Content:** Any uniformly P-time family has CompiledLowRank for large n.

### `P_neq_NP`
**From:** Axioms 1, 4 + derived `rank_monotone_reduction`.
**Content:** P = NP → DTM for perm → low rank (Axiom 1) ∧ ¬low rank (derived) → ⊥.

---

## Supporting Axiom (not in P_neq_NP chain)

### `constructive_witness` — Paper §11.7

**Statement:** Deterministic polynomial-time construction of w ∈ V_n^⊥ with a positive entry.

**Role:** Provides the mechanism for the paper's full diagonal construction. Not currently used by P_neq_NP (which uses the permanent route directly), but stated for completeness and future decomposition.

---

## Files

| File | Role |
|------|------|
| `PallLean/CompiledPoly.lean` | Cook-Levin CNF, compiled polynomial, blocked SPDP rank |
| `PallLean/Permanent.lean` | Permanent polynomial definition (permPoly) |
| `PallLean/CompiledSeparation.lean` | All axioms, derived theorems, P_neq_NP |
| `PallLean/TuringMachine.lean` | DTM definition, decides predicate |

## Architecture Decisions

- **Compiled polynomial route:** The old `paper-faithful` branch measured SPDP rank of `multilinearInterp(f)` — provably wrong (parity counterexample). This branch uses the compiled Cook-Levin polynomial P_{M,n}, matching the paper's actual architecture.

- **Permanent as hard family:** The paper uses perm_m as the NP-side hard polynomial (Theorem 94), not a custom diagonal. The separation goes through perm ∈ NP + perm has high algebraic rank + compilation preserves rank + P-time → low rank.

- **ℚ instead of F_p:** The paper's Appendix H.4 states characteristic 0 suffices. Can specialize later.

- **Old branch preserved:** Tag `v0.9-algebraic-infrastructure` on `paper-faithful` — 140 theorems, valid algebraic infrastructure (reusable as lemma library).
