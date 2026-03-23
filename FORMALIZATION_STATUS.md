# P ≠ NP Lean Formalization — Status Report

**Repository:** https://github.com/DarrenEdwards111/pall-lean  
**Branch:** `compiled-route`  
**Paper:** arXiv:2512.11820v5 (Edwards 2025), "Toward P ≠ NP via SPDP Framework"  
**Lean:** v4.28.0 + Mathlib  
**Commit:** `c90b3e4`

## Summary

The formalization proves the entire P ≠ NP separation framework conditional on
**two paper-core axioms** and **two technical axioms**. All surrounding algebra,
SPDP theory, extraction machinery, profile compression, and arithmetic is proved.

**8,938 lines of Lean 4 across 44 files. Zero sorries on-chain. Zero errors.**

## Axiom Inventory

### `#print axioms CompiledSeparation.P_neq_NP`

```
propext                          — standard Lean
Classical.choice                 — standard Lean
Quot.sound                       — standard Lean
CompiledSeparation.cookLevin_rank_bound    — paper §11-13
PneqNP_Paper.f_n_family_in_NP             — paper §8.6
SupportedDim.finrank_restrictSupportDeg_le — technical (proved, diamond-blocked)
ProfileCompression.scaffold_blockClosure_card_le — technical (concrete arithmetic)
```

### Paper-Core Axioms (irreducible mathematical content)

**1. `cookLevin_rank_bound`** — The Cook-Levin Embedding Theorem

The permanent polynomial's SPDP rank, when embedded into the compiled
variable space, is bounded by the violation polynomial's SPDP rank.
This is the core claim that a DTM deciding the hard family must encode
the permanent in its computation trace.

*Status:* Theorem stack decomposed (EncodingBridge.lean, CookLevinExtraction.lean).
Variable embedding and partition compatibility proved. The semantic core
(permanent generators ⊆ violation polynomial SPDP span) remains open.
Requires formalizing the full Cook-Levin reduction (~500+ lines).

**2. `f_n_family_in_NP`** — NP Membership of the Diagonal Family

The diagonal family f_n (defined as the sign of an SPDP annihilator) is in NP.

*Status:* **Fundamental soundness obstacle identified.** The family is defined
via `Classical.choice` selecting one specific annihilator from an
exponentially large orthogonal complement. An NP witness can certify
that *some* valid annihilator has positive weight at x, but this does
not imply the *chosen* annihilator has positive weight. Different valid
annihilators can disagree on sign. This is a genuine mathematical issue
with the proof architecture, not a formalization gap.

*Possible resolutions:*
- Canonical annihilator selection (requires poly-time reconstructibility)
- Redefine the hard family via witness-based condition (breaks escape theorem)
- Accept as irreducible axiom

### Technical Axioms (proved/provable, tooling-blocked)

**3. `finrank_restrictSupportDeg_le`** — Dimension Bound

`Module.finrank(restrictSupportDeg ℚ s d) ≤ (|s| + d)^|s|`

*Status:* **Fully proved** through the main import path. Axiomatized because
Lean 4 diamond import issue breaks the proof when imported through
CompiledSeparation → ProfileCompression → SupportedDim (different
instance resolution for `Set.Finite.pi`, `Finset.mem_coe`, etc.).

**4. `scaffold_blockClosure_card_le`** — Block Closure Bound

`|blockClosure(cellPartition, vars(violationPolyQ_ml))| ≤ 24`

*Status:* True bound is 8 (not 24). Scaffold vars at indices 0-7, each in own
block under cellPartition. Input tautology clauses produce constant 1 after
multilinearization (no vars). Formal proof requires ~200 lines of definitional
unfolding but is mathematically trivial.

## What Is Proved

- **SPDP theory:** Definitions, monotonicity, rank bounds, S-coupled shifts, transversal conditions
- **Permanent lower bound:** `permanentSpdpRank m ≥ m + 1` (identity minor argument)
- **Profile compression:** `restricted_clause_survival` — PROVED AND WIRED into P_neq_NP
- **Extraction machinery:** `rename_rank_le`, `iterDerivList_rename`, `blockedSpdpRankQ_mono_params`
- **Degree bounds:** `violationPolyQ_totalDegree ≤ 6`, multilinearization preserves degree
- **Variable support:** `vars_pderiv_subset`, `vars_iterDerivList_subset`, `iterDerivList_eq_zero_of_not_subset_vars`
- **Dimension bounds:** `spdp_span_in_restrictSupportDeg`, `finrank_restrictSupportDeg_le` (proved off-chain)
- **Encoding bridge:** `numVars_le_compiledVarCount`, `realToScaffold_injective`, `permEmbed_range_subset_input`, `permEmbed_blockOf`
- **P ≠ NP assembly:** Full proof chain from axioms through `extraction_rank_monotone`, `theorem92_scaffold_eventually`, to `P_neq_NP`

## Architecture

```
PneqNP_Paper.lean          — Main theorem: P ≠ NP
  ├── f_n_family_in_NP     — AXIOM: diagonal family ∈ NP
  └── P_subset_FSPDP       — P ⊆ FSPDP (from universal_spdp_collapse)

CompiledSeparation.lean    — Extraction + rank chain
  ├── cookLevin_rank_bound — AXIOM: permanent embeds in violation poly
  ├── extraction_rank_monotone — PROVED (rename_rank_le + mono_params)
  └── theorem92_scaffold_eventually — PROVED (restricted_clause_survival)

ProfileCompression.lean    — SPDP rank bound for violation polynomial
  └── restricted_clause_survival_from_ml — PROVED AND WIRED

PermanentLower.lean        — Permanent SPDP rank ≥ √n + 1
ExtractionDecomposition.lean — rename_rank_le (PROVED)
SupportedDim.lean          — Variable-restricted polynomial spaces
EncodingBridge.lean        — Real ↔ scaffold variable space bridge
RealTransition.lean        — DTM-dependent transition constraints
```

## Key Finding

The formalization exposed that **f_n_family_in_NP has a genuine mathematical
obstacle**: the nonconstructive annihilator selection via `Classical.choice`
creates a function whose NP membership cannot be established through standard
witness relations. This is not a formalization limitation — it is a structural
issue in the proof architecture that may require redefining the hard family
or the separation argument.
