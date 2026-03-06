#!/usr/bin/env python3
"""
Concrete SPDP rank computation for tiny Tseitin violation polynomial.

Setup: 3 disjoint 3-SAT clauses over 9 variables (x0..x8).
  g0 = (1-x0)(1-x1)(1-x2)
  g1 = (1-x3)(1-x4)(1-x5)  
  g2 = (1-x6)(1-x7)(1-x8)

Test 1: V = g0² + g1² + g2²  (sum of squares, no padding)
Test 2: P = ∏(1-z_c·g_c) for c=0,1,2 with selectors z9,z10,z11 (product form)
Test 3: Y·V where Y = z9·z10·z11  (padded violation)

For each, compute SPDP generators and rank for various κ.
"""

from itertools import combinations
from sympy import symbols, expand, diff, Poly, ZZ
from sympy.polys.orderings import lex
import numpy as np

# Variables
xs = symbols('x0:12')  # x0..x8 are clause vars, x9..x11 are selectors/padding

def clause_gadget(i):
    """(1-x_{3i})(1-x_{3i+1})(1-x_{3i+2})"""
    return (1 - xs[3*i]) * (1 - xs[3*i+1]) * (1 - xs[3*i+2])

def deriv_list(poly, var_indices):
    """Apply iterated partial derivatives."""
    p = expand(poly)
    for v in var_indices:
        p = diff(p, xs[v])
        if p == 0:
            return 0
    return expand(p)

def monomial_vector(poly, all_vars):
    """Convert polynomial to coefficient vector over monomials."""
    if poly == 0:
        return {}
    p = Poly(expand(poly), *all_vars)
    return {monom: coeff for monom, coeff in zip(p.monoms(), p.coeffs())}

def compute_spdp_rank(poly, kappa, var_indices, all_vars, max_ell=10):
    """Compute SPDP rank: dimension of span of {m · ∂^S(p)} generators.
    
    Simplified: just compute rank of matrix of ∂^S(p) for all admissible S.
    (Ignoring multiplier m and block admissibility for this test.)
    """
    derivatives = []
    for S in combinations(var_indices, kappa):
        d = deriv_list(poly, S)
        if d != 0:
            derivatives.append((S, d))
    
    if not derivatives:
        return 0, []
    
    # Collect all monomials
    all_monoms = set()
    vecs = []
    for S, d in derivatives:
        v = monomial_vector(d, all_vars)
        vecs.append(v)
        all_monoms.update(v.keys())
    
    all_monoms = sorted(all_monoms)
    monom_idx = {m: i for i, m in enumerate(all_monoms)}
    
    # Build matrix
    mat = np.zeros((len(vecs), len(all_monoms)), dtype=float)
    for i, v in enumerate(vecs):
        for m, c in v.items():
            mat[i, monom_idx[m]] = float(c)
    
    rank = np.linalg.matrix_rank(mat)
    return rank, [(S, d) for S, d in derivatives[:5]]  # return first 5 for display

print("=" * 60)
print("SPDP Rank Tests for Tseitin-like polynomials")
print("=" * 60)

g = [clause_gadget(i) for i in range(3)]

# Test 1: Sum of squares V = Σ g_c²
V = sum(expand(gi**2) for gi in g)
print("\n--- Test 1: V = Σ g_c² (sum of squares, no padding) ---")
clause_vars = list(range(9))
all_v = list(xs[:9])
for kappa in range(1, 5):
    rank, samples = compute_spdp_rank(V, kappa, clause_vars, all_v)
    print(f"  κ={kappa}: rank = {rank}, num nonzero derivs = {len(samples)}")
    if samples and kappa <= 2:
        for S, d in samples[:2]:
            print(f"    ∂{S}: {d}")

# Test 2: Product form P = ∏(1 - z_c · g_c)
z = [xs[9], xs[10], xs[11]]
P = expand((1 - z[0]*g[0]) * (1 - z[1]*g[1]) * (1 - z[2]*g[2]))
print("\n--- Test 2: P = ∏(1 - z_c·g_c) (product form) ---")
all_vars_12 = list(xs[:12])
all_indices = list(range(12))
for kappa in range(1, 5):
    rank, samples = compute_spdp_rank(P, kappa, all_indices, all_vars_12)
    print(f"  κ={kappa}: rank = {rank}")

# Test 3: Padded violation Y·V where Y = z9·z10·z11
Y = xs[9] * xs[10] * xs[11]
YV = expand(Y * V)
print("\n--- Test 3: Y·V (padded violation, Y = z9·z10·z11) ---")
for kappa in range(1, 5):
    rank, samples = compute_spdp_rank(YV, kappa, all_indices, all_vars_12)
    print(f"  κ={kappa}: rank = {rank}")

# Test 4: Direct comparison at κ=2
print("\n--- Test 4: κ=2 detailed comparison ---")
print("Sum of squares V:")
for S in [(0,3), (0,1), (3,4), (0,6)]:
    d = deriv_list(V, S)
    status = "NONZERO" if d != 0 else "ZERO"
    print(f"  ∂{S}(V) = {status}: {d if d != 0 else '0'}")

print("Product P:")
for S in [(9,0), (9,10), (0,3), (9,3)]:
    d = deriv_list(P, S)
    status = "NONZERO" if d != 0 else "ZERO"
    print(f"  ∂{S}(P) = {status}")

print("\nPadded Y·V:")
for S in [(9,0), (9,10), (0,3), (9,3)]:
    d = deriv_list(YV, S)
    status = "NONZERO" if d != 0 else "ZERO"
    print(f"  ∂{S}(Y·V) = {status}")
