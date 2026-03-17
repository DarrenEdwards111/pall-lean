# Trust Boundary — Compiled-Route Architecture

**Branch:** `compiled-route`
**Build:** 3136 jobs, 0 errors, 0 sorry
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
**Difficulty:** Medium. Genuine standalone theorem requiring dedicated infrastructure.

#### Failed Proof Avenues (stress-tested, 2026-03-17)

1. **V' ⊆ φ(V)** (image containment): Fails because shift monomials m using
   evaluated variables produce elements NOT in the image of φ. Concretely,
   if x_j is evaluated to c_j, the generator x_j · ∂^S(φ(p)) is not in
   {φ(q) : q ∈ V} since x_j ∉ image(φ).

2. **V' ⊆ V** (direct containment): Fails because V generators use ∂^S(p)
   while V' generators use ∂^S(φ(p)) — different polynomials, different spans.

3. **U' ⊆ U** (derivative span containment): Fails. φ(∂^S(p)) is NOT always
   in span{∂^{S'}(p)} — evaluation involves Taylor-expansion-like reconstruction,
   not just derivatives. Concrete counterexample: p = x₁ + x₂², φ: x₂→3,
   φ(p) = x₁+9 ∉ span{x₁+x₂², 1, x₂}.

4. **Per-component dimension bound**: For fixed S, dim(W·φ(q_S)) ≤ dim(W·q_S)
   holds (both = dim(W) when nonzero, by integral domain). But
   dim(Σ_S W·A_S) ≤ dim(Σ_S W·B_S) does NOT follow from per-S bounds —
   cross-S dependencies can differ.

5. **Kernel inclusion** (ker ⊆ ker'): If Σ c_i m_i q_{S_i} = 0, applying φ
   gives Σ c_i φ(m_i) φ(q_{S_i}) = 0, but we need Σ c_i m_i φ(q_{S_i}) = 0.
   The m_i vs φ(m_i) mismatch blocks this.

6. **Abstract linear algebra**: The analogous statement for arbitrary linear
   operators and arbitrary projections is FALSE (finite-dim counterexample
   constructed). The proof MUST use polynomial-specific structure.

#### Proof Sketch (correct but requires infrastructure)

The SPDP matrix M has rows indexed by admissible (S,m) pairs, columns by monomials.
Row (S,m) = coefficient vector of m · ∂^S(p).

For the evaluated polynomial φ(p):
- Rows with S containing evaluated variables → zeroed (∂_j(φ(p)) = 0)
- Rows with S non-evaluated → right-multiplied by coefficient-collapse matrix C
  (C merges monomials differing only in evaluated-variable exponents)

Both operations (row deletion, right-multiplication by C) are rank-non-increasing.
Combined: rank(M') ≤ rank(M).

**Infrastructure needed:**
- Coefficient vectors for MvPolynomial (monomial basis extraction)
- SPDP matrix construction (rows = generators, columns = monomials)
- Evaluation-induced column-collapse map C
- Rank monotonicity under row deletion + right multiplication
- Derivative-eval commutativity at coefficient level

This is a dedicated sub-project, not a quick theorem finish.

**Attack order:** Second (when coefficient-matrix infrastructure is built).

### Axiom 4: `perm_restriction_exists` — Structural Embedding

The permanent polynomial can be recovered from any compiled polynomial (of a DTM
deciding the hard NP family) by evaluating auxiliary variables.

**Paper:** Theorem 207 (rank-monotone block-local reduction).
**Difficulty:** Medium-High. Requires full Cook-Levin formalization.
**Content:** Irreducible reduction theorem — can't be decomposed without constructing
the actual Cook-Levin encoding (input/witness/trace variable structure, clause
generation from DTM transitions, semantic restriction recovering the permanent).
**Attack order:** After spdp_rank_eval_le (needs Cook-Levin infrastructure).

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

## Phase Summary

This trust boundary represents a **natural plateau**:
- Each remaining axiom is a distinct mathematical theorem requiring specialized infrastructure
- No axiom can be eliminated by clever rearrangement of existing lemmas
- The 5 proved theorems represent genuine deductive work (not just restatements)
- The axiom dependency graph is minimal (no redundant axioms)

### Next Phase Options (each is a sub-project)
1. **Coefficient-matrix layer** → eliminates Axiom 3 (spdp_rank_eval_le)
2. **Cook-Levin formalization** → eliminates Axiom 4 (perm_restriction_exists)
3. **Permanent SPDP analysis** → eliminates Axiom 2 (permanent_spdp_lower)
4. **Profile compression** → eliminates Axiom 1 (pside_compiled_collapse)
