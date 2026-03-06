#!/usr/bin/env python3
"""
Channel-based invariants for SPDP bridge.

Test candidate observables I(·) such that:
  I(product_NP) = superpolynomial
  I(sum_P) = polynomial

Candidates:
1. Interaction matrix rank (pairwise derivative correlations)
2. Diagonal coefficient pattern (Kronecker-δ signature)
3. Multilinear coefficient tensor rank
4. Packed clause correlation matrix
"""
import numpy as np
from itertools import combinations
from collections import defaultdict

# === Poly arithmetic ===
def poly_mul(p1,p2):
    r=defaultdict(int)
    for m1,c1 in p1.items():
        for m2,c2 in p2.items():
            if m1&m2: continue
            r[m1|m2]+=c1*c2
    return {m:c for m,c in r.items() if c}

def poly_add(p1,p2):
    r=defaultdict(int)
    for m,c in p1.items(): r[m]+=c
    for m,c in p2.items(): r[m]+=c
    return {m:c for m,c in r.items() if c}

def poly_neg(p): return {m:-c for m,c in p.items()}
def X(i): return {frozenset([i]):1}
def C(c): return {frozenset():c} if c else {}

def pderiv(p,v):
    r=defaultdict(int)
    for m,c in p.items():
        if v in m: r[m-{v}]+=c
    return {m:c for m,c in r.items() if c}

def coeff(p, monom):
    """Get coefficient of monomial (as frozenset)."""
    return p.get(monom, 0)

# === Polynomial builders ===
def build_product(n):
    """∏(1 - z_i·(x_{2i}+x_{2i+1})), z_i=1000+i"""
    p = C(1)
    for i in range(n):
        g = poly_add(X(2*i), X(2*i+1))
        p = poly_mul(p, poly_add(C(1), poly_neg(poly_mul(X(1000+i), g))))
    return p

def build_sum(n):
    """∑(x_{2i}+x_{2i+1})²"""
    p = {}
    for i in range(n):
        g = poly_add(X(2*i), X(2*i+1))
        p = poly_add(p, poly_mul(g, g))
    return p

def build_y_sum(n, kappa):
    """Y · ∑ G² where Y = y₁···y_κ"""
    s = build_sum(n)
    y = C(1)
    for k in range(kappa):
        y = poly_mul(y, X(5000+k))
    return poly_mul(y, s)

def build_y_product(n, kappa):
    """Y · ∏(1-z_i·G_i)"""
    p = build_product(n)
    y = C(1)
    for k in range(kappa):
        y = poly_mul(y, X(5000+k))
    return poly_mul(y, p)

# === Invariant 1: Interaction Matrix ===
def interaction_matrix(poly, blocks):
    """
    For each pair of blocks (i,j), compute:
    M[i,j] = ∂_{v_i}∂_{v_j}(poly) evaluated at coefficient level.
    
    Use first variable of each block as representative.
    Returns the matrix and its rank.
    """
    reps = [blk[0] for blk in blocks]
    n = len(reps)
    M = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            if i == j: continue
            d = pderiv(pderiv(poly, reps[i]), reps[j])
            # Use "size" of derivative as the entry
            M[i,j] = sum(abs(c) for c in d.values()) if d else 0
    return M, int(np.linalg.matrix_rank(M))

# === Invariant 2: Kronecker-δ signature ===
def kronecker_signature(poly, blocks, kappa):
    """
    For each κ-subset of blocks, take one derivative per block,
    then check the CONSTANT TERM of the result.
    
    For the product ∏(1-z_i·G_i), differentiating by z_{i1},...,z_{iκ}
    gives a constant term that is (-1)^κ · ∏ G_{ij} evaluated at some point.
    The diagonal pattern (choosing matching vars) gives nonzero;
    off-diagonal gives zero. This is the identity minor.
    
    Count: how many κ-subsets give nonzero constant term?
    """
    reps = [blk[0] for blk in blocks]
    nonzero_count = 0
    total = 0
    for combo in combinations(range(len(reps)), kappa):
        d = poly
        for bi in combo:
            d = pderiv(d, reps[bi])
            if not d: break
        total += 1
        if d and coeff(d, frozenset()) != 0:
            nonzero_count += 1
    return nonzero_count, total

# === Invariant 3: Derivative diversity ===
def derivative_diversity(poly, blocks, kappa):
    """
    Count the number of DISTINCT nonzero κ-fold derivatives
    (using one var per block). This is related to SPDP rank
    but measures diversity, not dimension.
    """
    reps = [blk[0] for blk in blocks]
    seen = set()
    for combo in combinations(range(len(reps)), kappa):
        d = poly
        for bi in combo:
            d = pderiv(d, reps[bi])
            if not d: break
        if d:
            # Hash by coefficient pattern
            sig = tuple(sorted(d.items()))
            seen.add(sig)
    return len(seen)

# === Invariant 4: Coefficient entropy ===
def coeff_entropy(poly):
    """Shannon entropy of the coefficient distribution."""
    if not poly: return 0
    coeffs = np.array([abs(c) for c in poly.values()], dtype=float)
    coeffs /= coeffs.sum()
    return -np.sum(coeffs * np.log2(coeffs + 1e-30))

# === Invariant 5: Packed interaction tensor ===
def packed_correlation(poly, blocks, kappa):
    """
    For disjoint packed blocks, compute the derivative and look at
    cross-correlations between the resulting monomials.
    
    Build matrix: rows = κ-subsets, columns = monomials after derivation.
    SVD singular values tell us about the "spectral complexity".
    Return top-k singular values.
    """
    reps = [blk[0] for blk in blocks]
    derivs = []
    for combo in combinations(range(len(reps)), kappa):
        d = poly
        for bi in combo:
            d = pderiv(d, reps[bi])
            if not d: break
        derivs.append(d if d else {})
    
    if not any(derivs): return [], 0
    
    all_m = sorted(set().union(*(d.keys() for d in derivs if d)),
                   key=lambda s:(len(s),tuple(sorted(s))))
    if not all_m: return [], 0
    mi = {m:i for i,m in enumerate(all_m)}
    mat = np.zeros((len(derivs), len(all_m)))
    for i,d in enumerate(derivs):
        for m,c in d.items(): mat[i,mi[m]]=c
    
    sv = np.linalg.svd(mat, compute_uv=False)
    rank = int(np.sum(sv > 1e-10))
    return sv[:min(5,len(sv))].tolist(), rank

# ===========================================================
print("=" * 70)
print("CHANNEL INVARIANT EXPERIMENTS")
print("=" * 70)

# Product blocks: z-vars
# Sum blocks: x-var pairs
def product_blocks(n): return [[1000+i] for i in range(n)]
def sum_blocks(n): return [[2*i, 2*i+1] for i in range(n)]

print("\n--- Invariant 1: Interaction Matrix Rank ---")
print(f"{'n':>3} {'prod_rank':>10} {'sum_rank':>10}")
for n in range(2, 8):
    pp = build_product(n)
    sp = build_sum(n)
    _, pr = interaction_matrix(pp, product_blocks(n))
    _, sr = interaction_matrix(sp, sum_blocks(n))
    print(f"{n:>3} {pr:>10} {sr:>10}")

print("\n--- Invariant 2: Kronecker-δ signature (nonzero constant terms) ---")
print(f"{'n':>3} {'κ':>3} {'prod_nz/total':>15} {'sum_nz/total':>15}")
for n in range(2, 7):
    for k in [2, 3]:
        if k > n: continue
        pnz, pt = kronecker_signature(build_product(n), product_blocks(n), k)
        snz, st = kronecker_signature(build_sum(n), sum_blocks(n), k)
        print(f"{n:>3} {k:>3} {pnz:>7}/{pt:<7} {snz:>7}/{st:<7}")

print("\n--- Invariant 3: Derivative diversity ---")
print(f"{'n':>3} {'κ':>3} {'prod_div':>10} {'sum_div':>10}")
for n in range(2, 7):
    for k in [1, 2]:
        pd = derivative_diversity(build_product(n), product_blocks(n), k)
        sd = derivative_diversity(build_sum(n), sum_blocks(n), k)
        print(f"{n:>3} {k:>3} {pd:>10} {sd:>10}")

print("\n--- Invariant 4: Coefficient entropy ---")
print(f"{'n':>3} {'prod_H':>10} {'sum_H':>10}")
for n in range(2, 8):
    ph = coeff_entropy(build_product(n))
    sh = coeff_entropy(build_sum(n))
    print(f"{n:>3} {ph:>10.3f} {sh:>10.3f}")

print("\n--- Invariant 5: Spectral profile (top singular values) ---")
print(f"{'n':>3} {'form':>5} {'rank':>5}  {'top SVs':>30}")
for n in [3, 4, 5, 6]:
    for form, builder, blocks_fn in [
        ("prod", build_product, product_blocks),
        ("sum", build_sum, sum_blocks)
    ]:
        sv, rk = packed_correlation(builder(n), blocks_fn(n), 2)
        sv_str = ', '.join(f'{v:.1f}' for v in sv[:4])
        print(f"{n:>3} {form:>5} {rk:>5}  [{sv_str}]")

print("\n--- Invariant 6: Y-padded comparison (κ=2) ---")
print("Y*product vs Y*sum, both with padding")
print(f"{'n':>3} {'Y*prod rank':>12} {'Y*sum rank':>12}  {'Y*prod div':>11} {'Y*sum div':>11}")
for n in range(2, 6):
    kappa = 2
    yp = build_y_product(n, kappa)
    ys = build_y_sum(n, kappa)
    yp_blocks = [[5000+k] for k in range(kappa)] + product_blocks(n)
    ys_blocks = [[5000+k] for k in range(kappa)] + sum_blocks(n)
    
    _, ypr = packed_correlation(yp, yp_blocks, 2)
    _, ysr = packed_correlation(ys, ys_blocks, 2)
    ypd = derivative_diversity(yp, yp_blocks, 2)
    ysd = derivative_diversity(ys, ys_blocks, 2)
    print(f"{n:>3} {ypr:>12} {ysr:>12}  {ypd:>11} {ysd:>11}")

print("\n" + "=" * 70)
print("Which invariant separates product from sum?")
print("=" * 70)
