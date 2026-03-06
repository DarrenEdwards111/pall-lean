#!/usr/bin/env python3
"""
SPDP Rank Explorer — numerical experiments to find viable bridge forms.

Tests different polynomial constructions and measures their SPDP rank
(dimension of the derivative space) to find a form that:
1. Has polynomial rank (P-side)
2. Contains extractable superpolynomial-rank substructure (NP-side)

The "fuzzy" approach: try many candidates, measure, find patterns.
"""

import numpy as np
from itertools import combinations, product as cart_product
from collections import defaultdict
import sympy
from sympy import symbols, Poly, ring, ZZ, QQ, Symbol, expand, diff, Rational
from sympy.polys.orderings import lex
import time

def make_vars(n):
    """Create n symbolic variables."""
    return symbols(' '.join(f'x{i}' for i in range(n)))

def spdp_derivatives(poly, variables, kappa, ell=None):
    """
    Compute all kappa-fold partial derivatives of poly.
    Returns the set of resulting polynomials (as expanded sympy exprs).
    """
    if ell is None:
        ell = len(variables)
    
    derivs = set()
    # Choose kappa variables (with replacement allowed for ell, but
    # for SPDP we choose kappa distinct variables from a subset of size ell)
    var_subset = variables[:ell] if ell <= len(variables) else variables
    
    for combo in combinations(range(len(var_subset)), kappa):
        d = poly
        for idx in combo:
            d = diff(d, var_subset[idx])
        d = expand(d)
        if d != 0:
            derivs.add(d)
    
    return derivs

def derivative_space_rank(poly, variables, kappa):
    """
    Compute the dimension of the vector space spanned by all
    kappa-fold partial derivatives of poly.
    
    This is the SPDP rank Γ_{κ,ℓ}(poly).
    """
    var_list = list(variables)
    
    # Collect all kappa-fold derivatives
    deriv_polys = []
    for combo in combinations(range(len(var_list)), kappa):
        d = poly
        for idx in combo:
            d = diff(d, var_list[idx])
        d = expand(d)
        if d != 0:
            deriv_polys.append(d)
    
    if not deriv_polys:
        return 0
    
    # Extract monomial basis
    all_monoms = set()
    for p in deriv_polys:
        p_poly = Poly(p, *var_list, domain='QQ')
        all_monoms.update(p_poly.as_dict().keys())
    
    all_monoms = sorted(all_monoms)
    if not all_monoms:
        return 0
    
    # Build coefficient matrix
    mat = np.zeros((len(deriv_polys), len(all_monoms)), dtype=float)
    for i, p in enumerate(deriv_polys):
        p_poly = Poly(p, *var_list, domain='QQ')
        coeffs = p_poly.as_dict()
        for j, m in enumerate(all_monoms):
            if m in coeffs:
                mat[i, j] = float(coeffs[m])
    
    # Rank = dimension of derivative space
    return np.linalg.matrix_rank(mat)


def test_product_form(n_clauses, kappa):
    """
    Product form: ∏_{i=1}^{n} (1 - z_i * G_i)
    where G_i = x_{3i} + x_{3i+1} + x_{3i+2} - 1
    Variables: z_0..z_{n-1}, x_0..x_{3n-1}
    """
    n = n_clauses
    all_vars = make_vars(n + 3*n)
    z = all_vars[:n]
    x = all_vars[n:]
    
    poly = 1
    for i in range(n):
        G_i = x[3*i] + x[3*i+1] + x[3*i+2] - 1
        poly = expand(poly * (1 - z[i] * G_i))
    
    rank = derivative_space_rank(poly, all_vars, kappa)
    return rank, len(all_vars)

def test_sum_form(n_clauses, kappa):
    """
    Sum form: ∑_{i=1}^{n} G_i²
    where G_i = x_{3i} + x_{3i+1} + x_{3i+2} - 1
    """
    n = n_clauses
    all_vars = make_vars(3*n)
    
    poly = 0
    for i in range(n):
        G_i = all_vars[3*i] + all_vars[3*i+1] + all_vars[3*i+2] - 1
        poly = expand(poly + G_i**2)
    
    rank = derivative_space_rank(poly, all_vars, kappa)
    return rank, len(all_vars)

def test_mixed_product_of_sums(n_clauses, block_size, kappa):
    """
    Mixed form: ∏_{b} (1 - ε_b * ∑_{i in block_b} G_i²)
    Product of blocks, each block is a sum of squares.
    """
    n = n_clauses
    n_blocks = max(1, n // block_size)
    all_vars_count = 3*n + n_blocks  # x vars + epsilon vars
    all_vars = make_vars(all_vars_count)
    x = all_vars[:3*n]
    eps = all_vars[3*n:]
    
    poly = 1
    for b in range(n_blocks):
        block_sum = 0
        for i in range(b * block_size, min((b+1) * block_size, n)):
            G_i = x[3*i] + x[3*i+1] + x[3*i+2] - 1
            block_sum = expand(block_sum + G_i**2)
        poly = expand(poly * (1 - eps[b] * block_sum))
    
    rank = derivative_space_rank(poly, all_vars, kappa)
    return rank, all_vars_count

def test_shared_variable_product(n_clauses, kappa):
    """
    Product with shared global variable:
    ∏_{i} (1 - s * z_i * G_i)
    where s is shared across all factors.
    
    The shared variable limits identity minor extraction.
    """
    n = n_clauses
    all_vars = make_vars(1 + n + 3*n)  # s, z_0..z_{n-1}, x_0..x_{3n-1}
    s = all_vars[0]
    z = all_vars[1:n+1]
    x = all_vars[n+1:]
    
    poly = 1
    for i in range(n):
        G_i = x[3*i] + x[3*i+1] + x[3*i+2] - 1
        poly = expand(poly * (1 - s * z[i] * G_i))
    
    rank = derivative_space_rank(poly, all_vars, kappa)
    return rank, len(all_vars)

def test_sequential_product(n_steps, kappa):
    """
    Sequential TM-style: ∏_t (1 - G_t)
    where G_t = x_t * x_{t+1} (shares variables with neighbors)
    
    Models TM compilation where consecutive gates share variables.
    """
    n = n_steps
    all_vars = make_vars(n + 1)  # x_0 through x_n
    
    poly = 1
    for t in range(n):
        G_t = all_vars[t] * all_vars[t+1]
        poly = expand(poly * (1 - G_t))
    
    rank = derivative_space_rank(poly, all_vars, kappa)
    return rank, n + 1

def test_fuzzy_bridge(n_clauses, kappa):
    """
    Fuzzy bridge: Y * ∏_i (1 - z_i * G_i) * ∑_i G_i²
    
    Product of: padding * NP-verifier * violation-sum
    The idea: violation sum "witnesses" the structure while
    the product provides the rank.
    """
    n = n_clauses
    k = kappa
    all_vars = make_vars(k + n + 3*n)
    y = all_vars[:k]
    z = all_vars[k:k+n]
    x = all_vars[k+n:]
    
    Y = 1
    for yi in y:
        Y = expand(Y * yi)
    
    prod_part = 1
    sum_part = 0
    for i in range(n):
        G_i = x[3*i] + x[3*i+1] + x[3*i+2] - 1
        prod_part = expand(prod_part * (1 - z[i] * G_i))
        sum_part = expand(sum_part + G_i**2)
    
    poly = expand(Y * prod_part)
    rank_prod = derivative_space_rank(poly, all_vars, kappa)
    
    poly2 = expand(Y * sum_part)
    rank_sum = derivative_space_rank(poly2, all_vars, kappa)
    
    return rank_prod, rank_sum, len(all_vars)


print("=" * 70)
print("SPDP RANK EXPLORER — Finding viable bridge forms")
print("=" * 70)

# Test 1: Product vs Sum for small cases
print("\n--- Test 1: Product vs Sum rank comparison ---")
print(f"{'n_clauses':>10} {'κ':>4} {'product_rank':>13} {'sum_rank':>10} {'n_vars':>7}")
for n in [2, 3, 4, 5]:
    for k in [1, 2]:
        try:
            rp, nv = test_product_form(n, k)
            rs, _ = test_sum_form(n, k)
            print(f"{n:>10} {k:>4} {rp:>13} {rs:>10} {nv:>7}")
        except Exception as e:
            print(f"{n:>10} {k:>4} ERROR: {e}")

# Test 2: Sequential (TM-style) product
print("\n--- Test 2: Sequential product (shared vars between neighbors) ---")
print(f"{'n_steps':>10} {'κ':>4} {'seq_rank':>10} {'n_vars':>7}")
for n in [3, 4, 5, 6, 7]:
    for k in [1, 2]:
        try:
            r, nv = test_sequential_product(n, k)
            print(f"{n:>10} {k:>4} {r:>10} {nv:>7}")
        except Exception as e:
            print(f"{n:>10} {k:>4} ERROR: {e}")

# Test 3: Shared global variable
print("\n--- Test 3: Product with shared global variable ---")
print(f"{'n_clauses':>10} {'κ':>4} {'shared_rank':>12} {'product_rank':>13}")
for n in [2, 3, 4]:
    for k in [1, 2]:
        try:
            rs, _ = test_shared_variable_product(n, k)
            rp, _ = test_product_form(n, k)
            print(f"{n:>10} {k:>4} {rs:>12} {rp:>13}")
        except Exception as e:
            print(f"{n:>10} {k:>4} ERROR: {e}")

# Test 4: Mixed product-of-sums
print("\n--- Test 4: Mixed product-of-sums ---")
print(f"{'n_clauses':>10} {'blk_sz':>7} {'κ':>4} {'mixed_rank':>11} {'n_vars':>7}")
for n in [4, 6]:
    for bs in [1, 2, 3]:
        for k in [1, 2]:
            try:
                r, nv = test_mixed_product_of_sums(n, bs, k)
                print(f"{n:>10} {bs:>7} {k:>4} {r:>11} {nv:>7}")
            except Exception as e:
                print(f"{n:>10} {bs:>7} {k:>4} ERROR: {e}")

# Test 5: Fuzzy bridge comparison
print("\n--- Test 5: Y*product vs Y*sum rank ---")
print(f"{'n_clauses':>10} {'κ':>4} {'Y*prod_rank':>12} {'Y*sum_rank':>11}")
for n in [2, 3, 4]:
    k = 1
    try:
        rp, rs, nv = test_fuzzy_bridge(n, k)
        print(f"{n:>10} {k:>4} {rp:>12} {rs:>11}")
    except Exception as e:
        print(f"{n:>10} {k:>4} ERROR: {e}")

print("\n" + "=" * 70)
print("Look for a form where rank grows faster than poly but extraction works")
print("=" * 70)
