# P ≠ NP Lean Formalization — Status Report

**Repository:** https://github.com/DarrenEdwards111/pall-lean  
**Branch:** `compiled-route`  
**Paper:** arXiv:2512.11820v5 (Edwards 2025), "Toward P ≠ NP via SPDP Framework"  
**Lean:** v4.28.0 + Mathlib  
**Commit:** `9172f94`

## Summary

**Two proof architectures**, both building to P ≠ NP:

### v2 (Paper-Faithful) — `PneqNP_v2.lean`
Matches the paper's actual structure (Theorem 15.1, A1-A5).
**2 custom axioms.** No diagonal, no Classical.choice for the hard family.

### v1 (Original) — `PneqNP_Paper.lean` + `CompiledSeparation.lean`
Diagonal-based architecture with full extraction machinery.
**4 custom axioms** (2 paper-core + 2 technical).
9,000+ lines of supporting infrastructure.

## v2 Axiom Inventory (recommended)

```
#print axioms PneqNP_v2.P_neq_NP

propext                              — standard Lean
Classical.choice                     — standard Lean  
Quot.sound                           — standard Lean
BoolCircuit.ptime_spdp_collapse      — Paper A2 / Theorem 6.1
PneqNP_v2.hard_np_family_exists      — Paper A3 / Theorem 10.1
```

### `ptime_spdp_collapse` — P-side rank collapse (Paper A2)

Every deterministic polynomial-time machine has compiled SPDP rank ≤ n^O(1).
This is the universal P-side upper bound from the paper's profile compression
/ switching-lemma argument (Theorem 6.1, §9).

### `hard_np_family_exists` — NP-side non-collapse (Paper A3)

There exists an NP family F such that F(n) ∉ FSPDP for all large n.
The paper constructs this via Tseitin formulas on expander graphs:
3-SAT is trivially in NP, and the Tseitin family has SPDP rank ≥ n^Θ(log n)
(Theorem 10.1), which exceeds the √n threshold for FSPDP membership.

## Key Finding: Architecture Mismatch

The v1 formalization used a **nonconstructive diagonal family** defined via
`Classical.choice`, selecting an annihilator from the orthogonal complement
of the FSPDP evaluation subspace. This approach:

1. Does not appear in the paper (the paper uses explicit Tseitin formulas)
2. Creates a fundamental soundness obstacle for NP membership: different valid
   annihilators disagree on sign, so a witness for "some valid w has w(x) > 0"
   does not certify the chosen annihilator's sign
3. Required two additional axioms (`f_n_family_in_NP`, `cookLevin_rank_bound`)
   that are not needed in the paper's architecture

The v2 architecture eliminates this mismatch entirely.

## What Is Proved (across both architectures)

- **SPDP theory:** Definitions, monotonicity, S-coupled shifts, transversal conditions
- **Permanent lower bound:** permanentSpdpRank m ≥ m + 1
- **Profile compression:** restricted_clause_survival (proved and wired into v1)
- **Extraction machinery:** rename_rank_le, iterDerivList_rename, blockedSpdpRankQ_mono_params
- **Degree bounds:** violationPolyQ_totalDegree ≤ 6, multilinearization
- **Variable support:** vars_pderiv_subset, vars_iterDerivList_subset
- **Dimension bounds:** spdp_span_in_restrictSupportDeg
- **Proper subspace:** fspdp_proper_subspace (via Möbius functional)
- **Annihilator construction:** spdp_annihilator_exists (escape theorem)
- **Encoding bridge:** numVars_le_compiledVarCount, realToScaffold_injective
- **DTM infrastructure:** Real transition clauses, execution semantics

## File Statistics

- **45 files**, 9,000+ lines of Lean 4
- **0 errors**, **0 sorries on-chain**
- v1: 4 custom axioms | v2: 2 custom axioms
