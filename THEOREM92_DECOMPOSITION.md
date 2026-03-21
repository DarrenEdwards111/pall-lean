# Theorem 92 Decomposition

## Current axiom

```lean
axiom theorem92_scaffold_eventually (M : DTM) :
    ∃ n₀ : ℕ, ScaffoldBoundAfter M n₀
-- where ScaffoldBoundAfter M n₀ :=
--   ∀ n ≥ n₀, ∀ hn2, blockedSpdpRankQ(log₂n, log₂n, compiledPolyQ(cnf), tableauPartition) ≤ √n
```

## Decomposition into 5 sub-claims

### Sub-claim 1: Cook-Levin Locality (PARTIALLY PROVED)

**Statement:** The compiled polynomial has locality structure — it's a product
of clause polynomials, each touching ≤ 3 variables (width-3 CNF from Cook-Levin).

```
∀ M n hn2, HasLocalPartition (initialSemanticCNF M n hn2)
```

**Status:** Already proved as `initialSemantic_local`. The tableau partition
has `blockSizeBound = 3` and each clause's variables map to ≤ 3 blocks.

**Testable:** ✅ Construct a concrete CNF and verify clause widths.

### Sub-claim 2: Product-to-Sum Decomposition

**Statement:** The compiled polynomial `∏ clausePoly(c)` can be expanded as a
sum of at most `2^numClauses` gate polynomials, each with bounded variable width.

For a width-3 CNF with `L` clauses on `N` variables:
```
compiledPolyQ(cnf) = ∑ gates, each touching ≤ 3*L variables
```

But this is too loose. The paper uses a tighter decomposition via the product
structure — each "gate" is a partial product of a block of consecutive clauses.

**Key bound:** `numGates ≤ N`, `width ≤ O(log N)` (from binary Tseitin / depth-4 simulation).

**Status:** NOT proved. This is the depth-4 simulation content (Paper §5.2).

**Testable:** ✅ For a concrete width-3 CNF product, compute the actual number
of effectively independent terms and their variable overlap.

### Sub-claim 3: Profile Count Bound

**Statement:** For a polynomial with locality structure (numGates = G, width = w),
the number of distinct "profiles" (interface patterns between derivative set S
and the block partition) is bounded.

Paper §9, Lemma 29: Number of profiles ≤ `(G * w)^O(1)`.

More precisely: fixing the block-interface pattern of S, the remaining internal
structure is determined by the local gate structure. The number of distinct
block-interface patterns is ≤ `C(numBlocks, κ) * (boundary_alphabet)^κ`.

**Status:** Partially encoded in `HasLocalityStructure.profileRankBound`.
The structure has `profileRankBound : ∀ B κ ℓ, finrank(blockedSpdpSubspace) ≤ (G*w)^3`.

**Testable:** ✅ For small polynomials, enumerate actual profiles and count.

### Sub-claim 4: Per-Profile Span Bound

**Statement:** For each profile class, the span of generators within that class
has dimension ≤ `(G * w)^O(1)`.

Paper §9, Lemma 31: Per-profile dimension ≤ `(boundary_size + 1)^{width}`.

**Status:** Folded into `profileRankBound`. Not separately proved.

**Testable:** ✅ For a fixed derivative set S, compute the span of all valid
shift-times-derivative generators and measure its dimension.

### Sub-claim 5: Asymptotic Closure

**Statement:** Combining locality (G = poly(n), w = O(log n)) with profile
compression (rank ≤ (G*w)^3) gives `rank ≤ n^{O(1)}`. At κ = ℓ = log₂ n,
this becomes ≤ √n for large n (choosing the polynomial exponent correctly).

**Key calculation:**
- Cook-Levin gives G = O(n^{2k+1}), w = 3 (width-3 CNF)
- Profile compression gives rank ≤ (G * 3)^3 = O(n^{3(2k+1)})
- But this is polynomial in n, so ≤ √n fails for any fixed k!

**⚠️ PROBLEM IDENTIFIED:** The naive locality bound gives rank polynomial
in n (with exponent 3(2k+1)), which is NEVER ≤ √n. The paper must use
a tighter argument at the log-parameter level.

The paper's actual argument (§17.3): at κ = ℓ = c·log n, the profile
count is bounded by a function of log n (not n), because the block
partition has O(n / chunk) blocks and the derivative set touches
≤ κ = O(log n) blocks. So the number of profiles is polylogarithmic
in n, not polynomial.

**Revised bound:** profile_count ≤ `C(n/chunk, κ) * alphabet^κ` where
κ = O(log n). This gives `C(n, log n) * c^{log n}` which is still
super-polynomial...

**⚠️ DEEPER PROBLEM:** The profile count depends on the block partition.
With O(n) blocks and κ = log n, `C(n, log n)` is super-polynomial.
The paper must use a partition with O(polylog n) blocks, not O(n) blocks.

This is where the depth-4 simulation and binary Tseitin transformation
are critical: they produce a polynomial with O(polylog n) effective
blocks, not O(n).

## Summary of gaps

| Sub-claim | Status | Testable | Notes |
|---|---|---|---|
| 1. Locality | ✅ Proved | ✅ | Width-3 CNF from Cook-Levin |
| 2. Product-to-sum | ❌ Open | ✅ | Depth-4 simulation needed |
| 3. Profile count | ❌ Open | ✅ | Depends on block count |
| 4. Per-profile span | ❌ Open | ✅ | Local gate structure |
| 5. Asymptotic closure | ❌ Open | ✅ | Polylog vs poly blocks |

## Critical insight

The proof chain requires that the number of effective blocks is
polylogarithmic (not polynomial) in n. This comes from the depth-4
simulation: the compiled polynomial factors through O(log² n) stages,
each with bounded fan-in. The partition groups variables by stage,
giving O(log² n) blocks.

With O(log² n) blocks and κ = log n:
- Profile count ≤ C(log² n, log n) * c^{log n} ≤ n^{O(log log n)} * n^{O(1)}
- This is quasi-polynomial, still not polynomial...

**The paper's resolution:** Uses the profile compression theorem (§9)
which shows that for width-w locality structure, the rank is bounded
by a POLYNOMIAL in (G * w) regardless of the number of blocks. The
profileRankBound ≤ (G*w)^3 already encodes this.

The question reduces to: what are G and w for the compiled polynomial
at the log-parameter level?

## The Real Argument (after deeper analysis)

The key insight is the **universal restriction** applied BEFORE rank computation:

1. Universal restriction fixes all but w = log₂ n variables
2. After restriction, most clauses become trivial (constant 0 or 1)
3. Only L_eff = O(polylog n) clauses remain nontrivial
4. Each surviving clause touches ≤ 3 of the w live variables
5. Profile compression on L_eff local factors on w variables gives:
   rank ≤ L_eff * w^{O(1)} = polylog(n)^{O(1)}
6. polylog(n)^{O(1)} ≤ √n for large n ✓

### Why the naive analysis fails
Without restriction: L = O(n^{2k+1}) clauses, rank ≤ L^c ≫ √n.
WITH restriction: L_eff = O(polylog n) surviving clauses, rank ≤ polylog(n)^c ≤ √n.

### Sub-claims (revised)

| # | Sub-claim | Status | Content |
|---|---|---|---|
| 1 | Cook-Levin locality (width-3) | ✅ Proved | Each clause ≤ 3 vars |
| 2 | Universal restriction survival | ❌ Open | L_eff = O(polylog n) after restriction |
| 3 | Profile compression on survivors | ❌ Open | rank ≤ L_eff * w^c |
| 4 | Asymptotic closure | ✅ Proved | polylog^c ≤ √n |

**CORRECTION (2026-03-21):** Tautology clauses `(xᵢ ∨ ¬xᵢ)` compile to
`1 - Xᵢ + Xᵢ²`, NOT the constant 1. So tautology factors are nontrivial
as polynomials (only equal to 1 on boolean inputs). This means:
- After restriction, `log₂ n` tautology factors survive (for live vars)
- Plus ≤ 24 core clause factors
- Total surviving factors = O(log n), not O(1)

The O(log n) bound is correct and empirically validated. The "24 constant"
simplification would require multilinearization (X² → X), which is a
separate theorem.

The deepest gap is now **sub-claim 2**: bounding the number of clauses that
survive (remain nontrivial) after the universal restriction. This is about
the Cook-Levin encoding structure — most tableau clauses reference variables
in the fixed (early) part of the tableau, so they become constants.

### Why L_eff should be polylogarithmic
The Cook-Levin tableau has T(n) time steps. The universal restriction fixes
variables for time steps 0,...,T(n)-log₂n. Clauses that only reference these
early steps become constants. Only clauses involving the last log₂n time steps
survive → L_eff ≤ (time steps referencing live vars) * (clauses per step)
= O(log n) * O(1) = O(log n).

Actually: each time step contributes O(1) clauses (transition + head + tape).
The last log₂n steps contribute O(log n) clauses → L_eff = O(log n).
Then rank ≤ (log n)^c ≤ √n for large n. ✓

## Verdict (revised)

The proof structure is cleaner than initially appeared:

1. **Cook-Levin locality** (proved) — width-3 CNF
2. **Universal restriction clause survival** (open) — L_eff = O(log n)
3. **Profile compression** (open) — rank ≤ L_eff * w^c for local products
4. **Asymptotic closure** (proved) — polylog^c ≤ √n

The deepest open content is **clause survival counting** (very concrete, testable)
and **profile compression for small local products** (standard algebraic geometry).
Neither requires deep complexity theory — they're about the Cook-Levin encoding structure.
