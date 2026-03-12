# Architecture Bug: P-Side Bound

## The Contradiction

Two theorems in the codebase contradict each other for large n:

1. **NP lower bound** (`np_ml_lower_bound` in MultilinearSPDP.lean):
   ```
   mlBlockedSpdpRank(tseitinPartition n)(κ)(κ)(tseitinPoly ℚ n) ≥ n^{log₂ n / 4}
   ```
   PROVED via identity minor + Kronecker transfer through mlProj.

2. **Tseitin upper bound** (axiom `tseitin_spdp_rank_bound` in MultilinearSPDP.lean):
   ```
   mlBlockedSpdpRank(tseitinPartition n)(κ)(κ)(tseitinPoly ℚ n) ≤ n^200
   ```
   AXIOM (was the target of ProfileCompression.lean).

For n ≥ 2^800: n^{log n / 4} = n^200 at n = 2^800, and for larger n the lower
bound exceeds n^200. **The axiom is FALSE.**

## Root Cause

The P-side chain goes:
```
compiled(verifierSheet) ≤ Tseitin ≤ n^200 [FALSE]
compiled(fullCompiled) ≤ n^215 [via add_lowDeg]
```

This tries to get a POLYNOMIAL upper bound on the compiled polynomial by
bounding it through the Tseitin polynomial. But:
- The Tseitin polynomial IS the hard NP witness
- Its mlBlockedSpdpRank IS superpolynomial (proved!)
- Bounding through it gives a vacuous bound

## What Should Happen

The P-side bound should come from the COMPILER's structure directly:

1. The compiled polynomial for a polytime TM M is a product of O(T(n)) local
   transition constraints, each involving O(1) variables.

2. Profile compression / locality arguments bound the SPDP rank of such
   structured products: the polynomial-time computation only creates
   O(poly(n)) distinct "types" of derivative interactions.

3. This bound applies to `fullCompiledPoly` AS A PRODUCT OF LOCAL CONSTRAINTS,
   not by decomposing it as `rename(tseitin) + violation`.

## Key Insight

The decomposition `fullCompiledPoly = verifierSheet + violationPoly` is
MATHEMATICALLY CORRECT but USELESS FOR UPPER BOUNDS because:
- `verifierSheet = rename(tseitinPoly)` has superpolynomial rank
- `mlBlockedSpdpRank(A + B) ≤ mlBlockedSpdpRank(A) + mlBlockedSpdpRank(B)`
  gives a superpolynomial bound

The compiled polynomial should instead be analyzed as:
```
fullCompiledPoly = ∏_{t=1}^{T(n)} gate_constraint_t(x)
```
where each gate constraint involves O(1) variables from adjacent time steps.
The PRODUCT structure (with local factors) is what enables polynomial rank bounds.

## Action Items

1. **DELETE** the axiom `tseitin_spdp_rank_bound` — it's false
2. **RESTRUCTURE** the P-side to bound `fullCompiledPoly` directly from
   compiler locality, NOT through the Tseitin polynomial
3. **ProfileCompression** machinery may be repurposed for the compiler
   product structure rather than the Tseitin product structure
4. The NP-side (`np_ml_lower_bound`) and extraction (`extraction_rank_monotone`)
   remain correct and unchanged
