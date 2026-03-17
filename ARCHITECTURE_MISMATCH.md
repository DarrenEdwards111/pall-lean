# Architecture Mismatch — Critical Finding (2026-03-17)

## The Problem

Our formalization measures SPDP rank of `multilinearInterp(f)` — the multilinear
polynomial that agrees with f on {0,1}^n. The paper (arXiv v5) measures SPDP rank
of the **compiled polynomial** P_{M,n} — the Cook-Levin encoding of the Turing
machine computation.

These are **fundamentally different objects**:

| Property | multilinearInterp(f) | Compiled P_{M,n} |
|----------|---------------------|-------------------|
| Variables | n (input bits) | N = Θ(n³) (Cook-Levin) |
| Structure | Raw truth table | Block-local from TM simulation |
| Parity rank at κ=w | ≥ 2^w (proved) | Controlled by profile compression |
| Locality | None | Each gate touches O(1) variables |

## Consequence

At κ = ℓ = w = log₂ n:
- **multilinearInterp(parity)** has SPDP rank ≥ 2^w > √n (our proved lower bound)
- Parity is P-time, so ptime_spdp_collapse claims rank ≤ √n
- **Contradiction** → our architecture is inconsistent

But the paper's compiled P_{M_parity, n} has locality structure from Cook-Levin.
The profile compression (Section 9) exploits this locality to bound the compiled
rank, avoiding the parity counterexample entirely.

## What's Valid

The following proved infrastructure is mathematically correct but aimed at
the wrong object (multilinearInterp instead of compiled polynomial):

- Möbius inversion lemmas (MobiusInversion.lean)
- Span dimension bounds (SpanDim.lean)
- Degree bounds (DegreeBounds.lean)
- Multilinear restriction (MultilinearRestrict.lean)
- Iterated derivative chain (IterDerivTopCoeff.lean)
- Boolean evaluation (BoolEval.lean)

The following are specifically tied to the multilinearInterp architecture
and would need replacement:

- Top coefficient extraction (top_coeff_zero_of_InFSPDP)
- Möbius functional escape (mobiusL_vanishes_on_InFSPDP)
- Rank lower bound via top coefficient (restrictedRank_ge_proved)
- Proper subspace via Möbius (fspdp_proper_subspace)
- SPDP annihilator construction
- Escape theorem (f_n_escapes_FSPDP)

## Paper's Actual Architecture (arXiv v5)

1. **Compiled polynomial** P_{M,n}: Cook-Levin encoding with block-locality
2. **P-side** (Theorem 92): Profile compression bounds Γ_{κ,ℓ}(P_{M,n}) ≤ poly(n)
3. **NP-side** (Theorem 94): Lower bound on the diagonal's compiled SPDP rank
4. **Constructive witness** (Section 11.7): Deterministic poly-time construction
   of w ∈ V_n^⊥ (not Möbius functional, not Classical.choice)
5. **Separation** (Theorem 207): Main result

## What Would Need to Change

1. Define the compiled polynomial P_{M,n} (Cook-Levin + Tseitin encoding)
2. Redefine InFSPDP in terms of compiled rank, not multilinearInterp rank
3. Replace Möbius escape with Section 11.7's constructive witness approach
4. Replace top-coefficient lower bound with the paper's NP-side (Theorem 94)
5. Keep ptime_spdp_collapse but restate for compiled polynomial
6. Prove f_n ∈ NP via the constructive witness (not via Classical.choice)

This is essentially a rewrite of the core proof architecture while keeping
the algebraic infrastructure (Möbius inversion, etc.) as library lemmas.
