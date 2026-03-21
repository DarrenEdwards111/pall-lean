# Paper Alignment Audit (2026-03-21)

## Critical Findings

Reading Darren's paper (pall v51) against the Lean formalization revealed
three structural mismatches between our `blockedSpdpRankQ` and Definition 2.3.

### 1. Block Partition: poly(n) blocks, not 3

**Paper (Section 3.2):** Each cell (t,i) in the computation tableau is a block.
With T(n) = n^c time steps and ~T tape positions, there are T² = poly(n)
blocks, each containing O(1) variables (tape bit, state bits, head position).

**Lean (CookLevin.lean):** `tableauPartition` has exactly 3 blocks using
`(v / 2) % 3`. This makes block-admissibility vacuous for κ ≥ 3.

**Impact:** The 3-block partition provides NO compression. The paper's argument
fundamentally relies on poly(n) blocks to limit how many variables S can touch.

### 2. Shift Monomial S-Coupling

**Paper (Definition 2.3):** "A shift monomial m ∈ T_ℓ is block-admissible if
each variable in supp(m) lies in a block that also contains some element of
the derivative support being acted upon."

This means m can ONLY use variables in blocks touched by S. With poly(n) blocks
and |S| ≤ κ cells, m accesses at most κ · O(1) variables.

**Lean (CompiledPoly.lean):** `(m.vars.image bp.blockOf).card ≤ ℓ`, which
only limits the NUMBER of blocks m touches, not WHICH blocks. There is no
coupling between m's blocks and S's blocks.

**Impact:** Without coupling, m can use any N ambient variables, inflating
rank to Θ(N^ℓ) even for trivial polynomials. Verified numerically:
- Single tautology, N=6, κ=ℓ=2: rank = 55 (should be ~O(1))
- Single tautology, N=20, κ=ℓ=2: rank = 461 (grows as ~2N²)

### 3. Multilinear Convention

**Paper (after Definition 2.2):** "Throughout, we work modulo the Boolean ideal
⟨x²ᵢ − xᵢ⟩, i.e. the coefficient vectors in M_{κ,ℓ}(f) are taken in the
multilinear monomial basis."

**Lean:** `compiledPolyQ` is the raw product polynomial in MvPolynomial.
Tautology (x ∨ ¬x) compiles to 1 − x + x², NOT 1.

**Impact:** Without multilinearization, tautology factors are nontrivial,
contributing O(n) extra factors. With multilinearization, they collapse to 1.

## Current Status

The `blockedSpdpRankQ` definition is kept as-is (ambient, uncoupled) because:
- It's an UPPER BOUND on the paper's rank (strictly more rows allowed)
- The NP-side extraction_rank_monotone comparison is valid (both sides use same definition)
- The P-side bound needs the cell-based partition + coupling to work

## What Needs to Happen

### Route A: Proper Cell-Based Partition (recommended)
1. Define `cellPartition` with poly(n) blocks (one per tableau cell)
2. With poly(n) blocks and κ = O(log n), the block-admissibility IS restrictive
3. S as a transversal touches ≤ κ cells, each with O(1) vars
4. The m block constraint `(m.vars.image bp.blockOf).card ≤ ℓ` limits m to ≤ ℓ blocks
5. Combined: m accesses at most ℓ · O(1) variables
6. Rank ≤ C(ℓ · O(1) + ℓ, ℓ) · (number of κ-transversals) = poly(n)

### Route B: Add Explicit S-Coupling (paper-literal)
1. Add condition: `∀ v ∈ m.vars, bp.blockOf v ∈ S.toFinset.image bp.blockOf`
2. This directly enforces m variables are in S-touched blocks
3. More restrictive than Route A (subsumes it)

### Route C: Multilinearize
1. Define multilinearization map (mod x² = x)
2. Prove SPDP rank is preserved/controlled under multilinearization
3. Tautology factors vanish, leaving only 24 core clauses

### Recommended Order
- Route A first (easiest, biggest impact)
- Route C second (cleans up the tautology issue)
- Route B if needed for tighter bounds

## P-Side Upper Bound Architecture (Paper §4.2)

The paper's key bound (equation 3):
  Γ^B_{κ,ℓ}(P_{M,n}) ≤ T² · |B| = n^O(1)

where B = {monomials of degree ≤ D in ≤ R variables}, |B| ≤ (R+D)^{D+1}.

This works because:
1. Each row m · ∂_S(P) decomposes into local pieces from O(κ) cells
2. Each cell contributes a basis of size |B| = poly(n)
3. Total: T² · |B| = poly(n) rows span the entire blocked SPDP matrix
4. Profile compression (Section 5) refines this further

The 3-block partition breaks step 1: with 3 blocks, ∂_S doesn't localize.
With poly(n) blocks (cell-based), ∂_S hits specific cells, enabling locality.
