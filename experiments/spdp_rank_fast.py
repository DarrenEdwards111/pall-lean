#!/usr/bin/env python3
"""
Fast SPDP rank computation using multilinear polynomials over GF(p).
Represents polynomials as coefficient dictionaries {monomial_tuple: coeff}.
Monomials are tuples of variable indices (sorted, no repeats = multilinear).
"""

import numpy as np
from itertools import combinations
from collections import defaultdict
import time

# Work over integers (or mod p for speed)
MOD = 997  # prime, 0 = use exact integers

def poly_mul(p1, p2):
    """Multiply two polynomials. Each is dict {frozenset(vars): coeff}."""
    result = defaultdict(int)
    for m1, c1 in p1.items():
        for m2, c2 in p2.items():
            # Multilinear: if vars overlap, skip (x_i^2 = 0 in multilinear)
            if m1 & m2:
                continue
            m = m1 | m2
            c = c1 * c2
            if MOD:
                c %= MOD
            result[m] += c
            if MOD:
                result[m] %= MOD
    # Remove zeros
    return {m: c for m, c in result.items() if c % MOD != 0} if MOD else {m: c for m, c in result.items() if c != 0}

def poly_add(p1, p2):
    """Add two polynomials."""
    result = defaultdict(int)
    for m, c in p1.items():
        result[m] += c
    for m, c in p2.items():
        result[m] += c
    if MOD:
        return {m: c % MOD for m, c in result.items() if c % MOD != 0}
    return {m: c for m, c in result.items() if c != 0}

def poly_scale(p, s):
    """Multiply polynomial by scalar."""
    if MOD:
        return {m: (c * s) % MOD for m, c in p.items() if (c * s) % MOD != 0}
    return {m: c * s for m, c in p.items() if c * s != 0}

def poly_neg(p):
    return poly_scale(p, -1)

def poly_var(i):
    """Variable x_i."""
    return {frozenset([i]): 1}

def poly_const(c):
    """Constant polynomial."""
    if c == 0:
        return {}
    return {frozenset(): c}

def pderiv(p, var):
    """Partial derivative of multilinear polynomial w.r.t. variable var."""
    result = defaultdict(int)
    for m, c in p.items():
        if var in m:
            new_m = m - {var}
            result[new_m] += c
            if MOD:
                result[new_m] %= MOD
    if MOD:
        return {m: c for m, c in result.items() if c % MOD != 0}
    return {m: c for m, c in result.items() if c != 0}

def multi_pderiv(p, var_list):
    """Iterated partial derivative."""
    result = p
    for v in var_list:
        result = pderiv(result, v)
        if not result:
            return {}
    return result

def spdp_rank(poly, n_vars, kappa):
    """
    Compute SPDP rank: dimension of span of all kappa-fold derivatives.
    """
    # Collect all kappa-subsets of variables
    derivs = []
    for combo in combinations(range(n_vars), kappa):
        d = multi_pderiv(poly, combo)
        if d:
            derivs.append(d)
    
    if not derivs:
        return 0
    
    # Collect all monomials
    all_monoms = set()
    for d in derivs:
        all_monoms.update(d.keys())
    all_monoms = sorted(all_monoms, key=lambda s: (len(s), sorted(s)))
    monom_idx = {m: i for i, m in enumerate(all_monoms)}
    
    # Build matrix
    mat = np.zeros((len(derivs), len(all_monoms)), dtype=np.float64)
    for i, d in enumerate(derivs):
        for m, c in d.items():
            mat[i, monom_idx[m]] = c
    
    return np.linalg.matrix_rank(mat)


# ============================================================
# Polynomial constructions
# ============================================================

def clause_gadget(base_var):
    """G_i = x_{3i} + x_{3i+1} + x_{3i+2} - 1"""
    p = poly_const(-1)
    for j in range(3):
        p = poly_add(p, poly_var(base_var + j))
    return p

def build_product_form(n_clauses):
    """
    ∏_{i=0}^{n-1} (1 - z_i * G_i)
    vars: z_0..z_{n-1} (indices 0..n-1), x_0..x_{3n-1} (indices n..4n-1)
    """
    n = n_clauses
    poly = poly_const(1)
    for i in range(n):
        z_i = poly_var(i)  # z variable
        G_i = clause_gadget(n + 3*i)  # x variables start at index n
        term = poly_add(poly_const(1), poly_neg(poly_mul(z_i, G_i)))
        poly = poly_mul(poly, term)
    return poly, 4*n

def build_sum_form(n_clauses):
    """∑ G_i²"""
    n = n_clauses
    poly = {}
    for i in range(n):
        G_i = clause_gadget(3*i)
        G_sq = poly_mul(G_i, G_i)
        poly = poly_add(poly, G_sq)
    return poly, 3*n

def build_sequential_product(n_steps):
    """
    ∏_t (1 - x_t * x_{t+1})  — TM-style, shared vars between neighbors
    """
    poly = poly_const(1)
    for t in range(n_steps):
        gate = poly_mul(poly_var(t), poly_var(t+1))
        term = poly_add(poly_const(1), poly_neg(gate))
        poly = poly_mul(poly, term)
    return poly, n_steps + 1

def build_shared_global_product(n_clauses):
    """
    ∏_i (1 - s * z_i * G_i)  — one global shared variable s
    var 0 = s, vars 1..n = z, vars n+1..4n = x
    """
    n = n_clauses
    s = poly_var(0)
    poly = poly_const(1)
    for i in range(n):
        z_i = poly_var(1 + i)
        G_i = clause_gadget(1 + n + 3*i)
        term = poly_add(poly_const(1), poly_neg(poly_mul(s, poly_mul(z_i, G_i))))
        poly = poly_mul(poly, term)
    return poly, 1 + 4*n

def build_mixed_product_of_local_sums(n_clauses, block_size):
    """
    ∏_b (1 - ε_b * ∑_{i in block} G_i²)
    Blocks of `block_size` clauses each.
    vars: eps_0..eps_{B-1}, x_0..x_{3n-1}
    """
    n = n_clauses
    B = max(1, (n + block_size - 1) // block_size)
    poly = poly_const(1)
    for b in range(B):
        block_sum = {}
        for i in range(b * block_size, min((b+1) * block_size, n)):
            G_i = clause_gadget(B + 3*i)  # x vars start after eps vars
            G_sq = poly_mul(G_i, G_i)
            block_sum = poly_add(block_sum, G_sq)
        eps_b = poly_var(b)
        factor = poly_add(poly_const(1), poly_neg(poly_mul(eps_b, block_sum)))
        poly = poly_mul(poly, factor)
    return poly, B + 3*n

def build_product_of_linear(n_factors):
    """
    ∏_i (1 - x_i)  — simplest product, fully disjoint
    """
    poly = poly_const(1)
    for i in range(n_factors):
        poly = poly_mul(poly, poly_add(poly_const(1), poly_neg(poly_var(i))))
    return poly, n_factors


# ============================================================
# Run experiments
# ============================================================
print("=" * 70)
print("SPDP RANK EXPLORER (fast multilinear)")
print("=" * 70)

print("\n--- 1: Simple disjoint product ∏(1-x_i) ---")
print(f"{'n':>5} {'κ=1':>6} {'κ=2':>6} {'κ=3':>6}")
for n in range(2, 9):
    ranks = []
    for k in range(1, 4):
        if k > n:
            ranks.append('-')
            continue
        p, nv = build_product_of_linear(n)
        r = spdp_rank(p, nv, k)
        ranks.append(str(r))
    print(f"{n:>5} {ranks[0]:>6} {ranks[1]:>6} {ranks[2]:>6}")

print("\n--- 2: Product form ∏(1-z_i*G_i) vs Sum form ∑G_i² ---")
print(f"{'n':>5} {'form':>8} {'κ=1':>6} {'κ=2':>6}")
for n in [2, 3, 4, 5]:
    for form_name, builder in [("product", build_product_form), ("sum", build_sum_form)]:
        ranks = []
        for k in [1, 2]:
            try:
                p, nv = builder(n)
                t0 = time.time()
                r = spdp_rank(p, nv, k)
                dt = time.time() - t0
                ranks.append(f"{r}")
                if dt > 10:
                    ranks.append("SLOW")
                    break
            except Exception as e:
                ranks.append(f"ERR")
        while len(ranks) < 2:
            ranks.append("-")
        print(f"{n:>5} {form_name:>8} {ranks[0]:>6} {ranks[1]:>6}")

print("\n--- 3: Sequential product (TM-style, shared vars) ---")
print(f"{'n':>5} {'κ=1':>6} {'κ=2':>6} {'κ=3':>6}")
for n in range(3, 9):
    ranks = []
    for k in [1, 2, 3]:
        try:
            p, nv = build_sequential_product(n)
            r = spdp_rank(p, nv, k)
            ranks.append(str(r))
        except:
            ranks.append("-")
    print(f"{n:>5} {ranks[0]:>6} {ranks[1]:>6} {ranks[2]:>6}")

print("\n--- 4: Shared global variable product ---")
print(f"{'n':>5} {'κ=1':>6} {'κ=2':>6}  (vs disjoint product)")
for n in [2, 3, 4, 5]:
    ranks_s = []
    ranks_d = []
    for k in [1, 2]:
        try:
            ps, nvs = build_shared_global_product(n)
            rs = spdp_rank(ps, nvs, k)
            ranks_s.append(str(rs))
            pd, nvd = build_product_form(n)
            rd = spdp_rank(pd, nvd, k)
            ranks_d.append(str(rd))
        except:
            ranks_s.append("-")
            ranks_d.append("-")
    print(f"{n:>5} {ranks_s[0]:>6} {ranks_s[1]:>6}  (disj: {ranks_d[0]:>4} {ranks_d[1]:>4})")

print("\n--- 5: Mixed product-of-sums (block_size varies) ---")
print(f"{'n':>5} {'bs':>4} {'κ=1':>6} {'κ=2':>6}")
for n in [4, 6]:
    for bs in [1, 2, n]:
        ranks = []
        for k in [1, 2]:
            try:
                p, nv = build_mixed_product_of_local_sums(n, bs)
                r = spdp_rank(p, nv, k)
                ranks.append(str(r))
            except:
                ranks.append("-")
        print(f"{n:>5} {bs:>4} {ranks[0]:>6} {ranks[1]:>6}")

print("\n" + "=" * 70)
print("Key question: Is there a form with poly rank where extraction works?")
print("=" * 70)
