#!/usr/bin/env python3
"""
Probe the P-side question: what distinguishes NP-complete SAT from 
easy SAT in terms of Möbius structure?

Unit clauses: in P, but high Möbius mass. Why easy?
- MUSes are all size 2 (contradictory pairs)
- MUS structure is DECOMPOSABLE: independent pairs
- No interaction between different MUSes
- The Möbius mass is concentrated at level 2

3-SAT near threshold: NP-complete. What's different?
- MUSes of ALL sizes exist
- MUSes OVERLAP (share clauses)
- The Möbius structure has depth > 2
- Mass is spread across many levels

Hypothesis: the P-side bound should target the DEPTH and OVERLAP
of the MUS structure, not just the total mass.

A poly-time solver can produce mass at level 2 (pairwise), but
generating mass at level k requires handling k-way interactions,
which may require exponential time for NP-complete instances.

Let's test this experimentally.
"""

from itertools import combinations, product as cartesian_product

def is_satisfiable(clauses, n):
    """Check if a CNF formula is satisfiable by brute force."""
    for x in cartesian_product([0, 1], repeat=n):
        if all(evaluate_clause(c, x) for c in clauses):
            return True
    return False

def evaluate_clause(clause, x):
    for var_idx, positive in clause:
        if positive and x[var_idx] == 1:
            return True
        if not positive and x[var_idx] == 0:
            return True
    return False

def sat_decision(pool, z):
    """Decision function: SAT(active clauses where z_i = 1)."""
    active = [pool[i] for i in range(len(pool)) if z[i]]
    if not active:
        return True
    n = max(v for c in pool for v, _ in c) + 1
    return is_satisfiable(active, n)

def mobius_coeff(pool, S):
    """Möbius coefficient f̂(S) for subset S."""
    S = list(S)
    m = len(pool)
    val = 0
    for r in range(len(S) + 1):
        for T in combinations(S, r):
            T_set = set(T)
            sign = (-1) ** (len(S) - len(T_set))
            z = [1 if i in T_set else 0 for i in range(m)]
            f = 1 if sat_decision(pool, z) else 0
            val += sign * f
    return val

def mobius_spectrum(pool):
    """Compute full Möbius spectrum: nonzero coefficients by level."""
    m = len(pool)
    spectrum = {}
    for size in range(1, m + 1):
        count = 0
        for S in combinations(range(m), size):
            c = mobius_coeff(pool, S)
            if c != 0:
                count += 1
        if count > 0:
            spectrum[size] = count
    return spectrum

def mus_count(pool, n):
    """Count MUSes by size."""
    m = len(pool)
    muses = {}
    for size in range(1, m + 1):
        count = 0
        for S in combinations(range(m), size):
            active = [pool[i] for i in S]
            if is_satisfiable(active, n):
                continue
            # S is UNSAT — check minimality
            is_min = True
            for i in range(len(S)):
                subset = list(S[:i]) + list(S[i+1:])
                sub_active = [pool[j] for j in subset]
                if not is_satisfiable(sub_active, n):
                    is_min = False
                    break
            if is_min:
                count += 1
        if count > 0:
            muses[size] = count
    return muses

# Test 1: Unit clauses (easy SAT)
print("=" * 60)
print("UNIT CLAUSES (in P)")
print("n=3: (x0)(¬x0)(x1)(¬x1)(x2)(¬x2)")
print("=" * 60)
pool_unit = [[(0, True)], [(0, False)], [(1, True)], [(1, False)], [(2, True)], [(2, False)]]
n = 3
print(f"MUSes: {mus_count(pool_unit, n)}")
print(f"Möbius spectrum: {mobius_spectrum(pool_unit)}")

# Test 2: 3-SAT hard instance (small)
print(f"\n{'=' * 60}")
print("3-SAT HARD INSTANCE")
print("n=3, m=8 (near threshold ratio 8/3 ≈ 2.67)")
print("=" * 60)
pool_3sat = [
    [(0, True), (1, True), (2, True)],     # x0 ∨ x1 ∨ x2
    [(0, False), (1, False), (2, False)],   # ¬x0 ∨ ¬x1 ∨ ¬x2
    [(0, True), (1, False), (2, True)],     # x0 ∨ ¬x1 ∨ x2
    [(0, False), (1, True), (2, False)],    # ¬x0 ∨ x1 ∨ ¬x2
    [(0, True), (1, True), (2, False)],     # x0 ∨ x1 ∨ ¬x2
    [(0, False), (1, False), (2, True)],    # ¬x0 ∨ ¬x1 ∨ x2
    [(0, True), (1, False), (2, False)],    # x0 ∨ ¬x1 ∨ ¬x2
    [(0, False), (1, True), (2, True)],     # ¬x0 ∨ x1 ∨ x2
]
n = 3
print(f"MUSes: {mus_count(pool_3sat, n)}")
print(f"Möbius spectrum: {mobius_spectrum(pool_3sat)}")

# Test 3: UNSAT 3-SAT (all 8 possible 3-clauses on 3 vars)
print(f"\n{'=' * 60}")
print("UNSAT 3-SAT (all 8 clauses on 3 vars)")
print("=" * 60)
# This IS unsatisfiable
pool_all = []
for signs in cartesian_product([True, False], repeat=3):
    pool_all.append([(i, signs[i]) for i in range(3)])
n = 3
print(f"SAT check: {is_satisfiable(pool_all, n)}")
print(f"MUSes: {mus_count(pool_all, n)}")
print(f"Möbius spectrum: {mobius_spectrum(pool_all)}")

# Test 4: 2-SAT (in P but can have complex MUS structure)
print(f"\n{'=' * 60}")
print("2-SAT (in P)")
print("n=3: all 12 possible 2-clauses on 3 vars")
print("=" * 60)
pool_2sat = []
for i, j in combinations(range(3), 2):
    for si in [True, False]:
        for sj in [True, False]:
            pool_2sat.append([(i, si), (j, sj)])
n = 3
print(f"m = {len(pool_2sat)}")
print(f"MUSes: {mus_count(pool_2sat, n)}")
spec = mobius_spectrum(pool_2sat)
print(f"Möbius spectrum: {spec}")
print(f"Max nonzero level: {max(spec.keys()) if spec else 0}")

print(f"\n{'=' * 60}")
print("ANALYSIS")
print("=" * 60)
print("""
Key question: What structural property of the Möbius spectrum
distinguishes NP-complete from P-time computable instances?

Candidates:
1. MAX LEVEL: depth of the deepest nonzero coefficient
2. OVERLAP: how many MUSes share clauses
3. INTERACTION PATTERN: whether MUSes form a "tangled" structure
   vs decomposable independent blocks
4. GROWTH RATE: how fast the mass grows with formula size

The P-side theorem should state:
  "A poly-time compiled search polynomial can only generate
   Möbius mass at levels ≤ f(time), where f grows slowly."

Or equivalently:
  "For NP-complete families, the required Möbius depth exceeds
   any polynomial in the formula description length."
""")
