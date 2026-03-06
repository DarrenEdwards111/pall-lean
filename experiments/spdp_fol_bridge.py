#!/usr/bin/env python3
"""
Flower-of-Life / Lattice Bridge: numerical SPDP rank test.

Three families:
1. Pure sum: Y · ∑ G_i²           (rank ~ O(n))
2. Pure product: Y · ∏(1-z_i·G_i)  (rank ~ C(n,κ))
3. Lattice bridge: Y · ∏_b H_b     (rank ~ ???)

H_b = 1 - ∑_{i∈N(b)} z_i·G_i - λ·∑_{(i,j)∈E_b} G_i·G_j

Overlap patterns:
A. Chain: block b covers clauses {b, b+1} (overlap = 1 clause)
B. Grid: block b covers clauses {b, b+1, b+k} (2D lattice)
C. Flower: block b covers clause b + nearest 2 neighbors (degree 2)
"""
import numpy as np
from itertools import combinations
from collections import defaultdict

def poly_mul(p1,p2):
    r=defaultdict(int)
    for m1,c1 in p1.items():
        for m2,c2 in p2.items():
            if m1&m2:continue
            r[m1|m2]+=c1*c2
    return {m:c for m,c in r.items() if c}

def poly_add(p1,p2):
    r=defaultdict(int)
    for m,c in p1.items():r[m]+=c
    for m,c in p2.items():r[m]+=c
    return {m:c for m,c in r.items() if c}

def poly_neg(p): return {m:-c for m,c in p.items()}
def poly_scale(p,s): return {m:c*s for m,c in p.items() if c*s}
def X(i): return {frozenset([i]):1}
def C(c): return {frozenset():c} if c else {}

def pderiv(p,v):
    r=defaultdict(int)
    for m,c in p.items():
        if v in m: r[m-{v}]+=c
    return {m:c for m,c in r.items() if c}

def spdp_rank(poly, variables, kappa):
    derivs = []
    for combo in combinations(variables, kappa):
        d = poly
        for v in combo:
            d = pderiv(d, v)
            if not d: break
        if d: derivs.append(d)
    if not derivs: return 0
    all_m = sorted(set().union(*(d.keys() for d in derivs)), key=lambda s:(len(s),tuple(sorted(s))))
    mi = {m:i for i,m in enumerate(all_m)}
    mat = np.zeros((len(derivs),len(all_m)))
    for i,d in enumerate(derivs):
        for m,c in d.items(): mat[i,mi[m]]=c
    return int(np.linalg.matrix_rank(mat))

def get_vars(p):
    return sorted(set().union(*(m for m in p.keys() if m))) if p else []

# Clause gadget: G_i = x_{2i} · x_{2i+1} (AND, disjoint vars)
def G(i):
    return poly_mul(X(2*i), X(2*i+1))

# === PURE SUM ===
def build_sum(n):
    """∑ G_i"""
    p = {}
    for i in range(n):
        p = poly_add(p, G(i))
    return p

# === PURE PRODUCT ===
def build_product(n):
    """∏(1 - G_i)"""
    p = C(1)
    for i in range(n):
        p = poly_mul(p, poly_add(C(1), poly_neg(G(i))))
    return p

# === LATTICE BRIDGE: Chain overlap ===
def build_chain_bridge(n, lam=1):
    """
    ∏_{b=0}^{n-2} H_b where H_b = 1 - G_b - G_{b+1} - λ·G_b·G_{b+1}
    
    Each block covers 2 adjacent clauses with overlap.
    Block b and block b+1 share clause b+1.
    """
    if n < 2: return C(1)
    p = C(1)
    for b in range(n-1):
        Hb = C(1)
        Hb = poly_add(Hb, poly_neg(G(b)))
        Hb = poly_add(Hb, poly_neg(G(b+1)))
        Hb = poly_add(Hb, poly_scale(poly_neg(poly_mul(G(b), G(b+1))), lam))
        p = poly_mul(p, Hb)
    return p

# === LATTICE BRIDGE: Disjoint blocks (no overlap) ===
def build_disjoint_bridge(n, lam=1):
    """
    ∏_{b=0}^{n/2-1} H_b where H_b = 1 - G_{2b} - G_{2b+1} - λ·G_{2b}·G_{2b+1}
    
    Each block covers 2 clauses, NO overlap between blocks.
    """
    p = C(1)
    for b in range(n // 2):
        i, j = 2*b, 2*b+1
        Hb = C(1)
        Hb = poly_add(Hb, poly_neg(G(i)))
        Hb = poly_add(Hb, poly_neg(G(j)))
        Hb = poly_add(Hb, poly_scale(poly_neg(poly_mul(G(i), G(j))), lam))
        p = poly_mul(p, Hb)
    return p

# === LATTICE BRIDGE: Simple overlap (each clause in 2 blocks) ===
def build_overlap_bridge(n, lam=1):
    """
    ∏_{b=0}^{n-1} H_b where H_b = 1 - G_b - λ·G_b·G_{(b+1)%n}
    
    Each block centers on one clause but couples to its neighbor.
    Circular topology: clause n-1 couples to clause 0.
    """
    p = C(1)
    for b in range(n):
        nb = (b + 1) % n
        Hb = poly_add(C(1), poly_neg(G(b)))
        Hb = poly_add(Hb, poly_scale(poly_neg(poly_mul(G(b), G(nb))), lam))
        p = poly_mul(p, Hb)
    return p

# === LATTICE BRIDGE: Minimal linear (1 - G_b) with overlap through shared vars ===
def build_shared_var_bridge(n):
    """
    ∏(1 - G'_b) where G'_b = x_{b} · x_{b+1} (overlapping variable sets)
    
    This is the chain product from earlier experiments.
    """
    p = C(1)
    for b in range(n):
        gb = poly_mul(X(b), X(b+1))
        p = poly_mul(p, poly_add(C(1), poly_neg(gb)))
    return p


print("=" * 70)
print("FLOWER-OF-LIFE BRIDGE: SPDP RANK COMPARISON")
print("=" * 70)

print(f"\n{'n':>3} {'κ':>3} | {'sum':>6} {'product':>8} {'chain_br':>9} {'disj_br':>8} {'overlap':>8} {'shared':>7}")
print("-" * 65)

for n in range(3, 9):
    for kappa in [1, 2, 3]:
        sp = build_sum(n)
        pp = build_product(n)
        cb = build_chain_bridge(n)
        db = build_disjoint_bridge(n)
        ob = build_overlap_bridge(n)
        sb = build_shared_var_bridge(n)
        
        sv = get_vars(sp)
        pv = get_vars(pp)
        cv = get_vars(cb)
        dv = get_vars(db)
        ov = get_vars(ob)
        sbv = get_vars(sb)
        
        sr = spdp_rank(sp, sv, kappa) if len(sv) >= kappa else 0
        pr = spdp_rank(pp, pv, kappa) if len(pv) >= kappa else 0
        cr = spdp_rank(cb, cv, kappa) if len(cv) >= kappa else 0
        dr = spdp_rank(db, dv, kappa) if len(dv) >= kappa else 0
        orr = spdp_rank(ob, ov, kappa) if len(ov) >= kappa else 0
        sbr = spdp_rank(sb, sbv, kappa) if len(sbv) >= kappa else 0
        
        print(f"{n:>3} {kappa:>3} | {sr:>6} {pr:>8} {cr:>9} {dr:>8} {orr:>8} {sbr:>7}")
    print()

print("\n" + "=" * 70)
print("ANALYSIS")
print("=" * 70)
print("""
Key question: Is there a bridge form where rank is:
  - LARGER than sum (has cross-clause interaction)
  - SMALLER than pure product (controlled by overlap degree)
  - Still superpolynomial for large n?

The lattice bridge must be in a "Goldilocks zone":
  sum << bridge << product
""")

# Detailed analysis of chain bridge with varying lambda
print("\n--- Chain bridge: effect of coupling strength λ ---")
print(f"{'n':>3} {'λ':>5} {'κ=2':>6} {'κ=3':>6}")
for n in [4, 5, 6]:
    for lam in [0, 1, 2, 5]:
        cb = build_chain_bridge(n, lam)
        cv = get_vars(cb)
        r2 = spdp_rank(cb, cv, 2) if len(cv) >= 2 else 0
        r3 = spdp_rank(cb, cv, 3) if len(cv) >= 3 else 0
        print(f"{n:>3} {lam:>5} {r2:>6} {r3:>6}")
    print()

# Term count comparison
print("\n--- Term count (polynomial size) ---")
print(f"{'n':>3} {'sum':>6} {'product':>8} {'chain_br':>9} {'overlap':>8}")
for n in range(3, 9):
    print(f"{n:>3} {len(build_sum(n)):>6} {len(build_product(n)):>8} {len(build_chain_bridge(n)):>9} {len(build_overlap_bridge(n)):>8}")
