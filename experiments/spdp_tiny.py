#!/usr/bin/env python3
"""Tiny SPDP rank experiments — n ≤ 4 clauses only."""
import numpy as np
from itertools import combinations
from collections import defaultdict
import time

MOD = 0  # exact integers

def poly_mul(p1, p2):
    result = defaultdict(int)
    for m1, c1 in p1.items():
        for m2, c2 in p2.items():
            if m1 & m2: continue  # multilinear
            result[m1 | m2] += c1 * c2
    return {m: c for m, c in result.items() if c != 0}

def poly_add(p1, p2):
    result = defaultdict(int)
    for m, c in p1.items(): result[m] += c
    for m, c in p2.items(): result[m] += c
    return {m: c for m, c in result.items() if c != 0}

def poly_neg(p):
    return {m: -c for m, c in p.items()}

def X(i):
    return {frozenset([i]): 1}

def C(c):
    return {frozenset(): c} if c else {}

def pderiv(p, v):
    result = defaultdict(int)
    for m, c in p.items():
        if v in m:
            result[m - {v}] += c
    return {m: c for m, c in result.items() if c != 0}

def spdp_rank(poly, n_vars, kappa):
    derivs = []
    for combo in combinations(range(n_vars), kappa):
        d = poly
        for v in combo:
            d = pderiv(d, v)
            if not d: break
        if d: derivs.append(d)
    if not derivs: return 0
    all_m = sorted(set().union(*(d.keys() for d in derivs)), key=lambda s: (len(s), tuple(sorted(s))))
    mi = {m: i for i, m in enumerate(all_m)}
    mat = np.zeros((len(derivs), len(all_m)))
    for i, d in enumerate(derivs):
        for m, c in d.items():
            mat[i, mi[m]] = c
    return int(np.linalg.matrix_rank(mat))

# Simple linear gadget: G_i uses vars {2i, 2i+1} (width 2 to keep small)
def gadget(i):
    """G_i = x_{2i} + x_{2i+1}"""
    return poly_add(X(2*i), X(2*i+1))

print("=" * 60)
print("SPDP RANK — TINY EXPERIMENTS (width-2 gadgets)")
print("=" * 60)

# PRODUCT: ∏(1 - z_i * G_i), z_i at index 100+i
print("\n--- Product ∏(1 - z_i·G_i) ---")
for n in range(1, 7):
    p = C(1)
    nv_max = 0
    for i in range(n):
        zi = X(100 + i)
        gi = gadget(i)
        term = poly_add(C(1), poly_neg(poly_mul(zi, gi)))
        p = poly_mul(p, term)
        nv_max = max(nv_max, 2*i+1, 100+i)
    
    all_vars = sorted(set().union(*(m for m in p.keys() if m)))
    nv = len(all_vars)
    # remap vars to 0..nv-1
    vmap = {v: j for j, v in enumerate(all_vars)}
    p2 = {}
    for m, c in p.items():
        p2[frozenset(vmap[v] for v in m)] = c
    
    ranks = []
    for k in [1, 2, 3]:
        if k > nv: ranks.append("-"); continue
        t0 = time.time()
        r = spdp_rank(p2, nv, k)
        dt = time.time() - t0
        if dt > 5:
            ranks.append(f"{r}*")
            break
        ranks.append(str(r))
    print(f"  n={n}: vars={nv}, rank(κ=1,2,3) = {', '.join(ranks)}, #terms={len(p)}")

# SUM: ∑ G_i²
print("\n--- Sum ∑ G_i² ---")
for n in range(1, 7):
    p = {}
    for i in range(n):
        gi = gadget(i)
        p = poly_add(p, poly_mul(gi, gi))
    nv = 2 * n
    ranks = []
    for k in [1, 2, 3]:
        if k > nv: ranks.append("-"); continue
        r = spdp_rank(p, nv, k)
        ranks.append(str(r))
    print(f"  n={n}: vars={nv}, rank(κ=1,2,3) = {', '.join(ranks)}, #terms={len(p)}")

# SEQUENTIAL: ∏(1 - x_t · x_{t+1})
print("\n--- Sequential ∏(1 - x_t·x_{t+1}) ---")
for n in range(2, 8):
    p = C(1)
    for t in range(n):
        gate = poly_mul(X(t), X(t+1))
        p = poly_mul(p, poly_add(C(1), poly_neg(gate)))
    nv = n + 1
    ranks = []
    for k in [1, 2, 3]:
        if k > nv: ranks.append("-"); continue
        t0 = time.time()
        r = spdp_rank(p, nv, k)
        if time.time() - t0 > 5:
            ranks.append(f"{r}*"); break
        ranks.append(str(r))
    print(f"  n={n}: vars={nv}, rank(κ=1,2,3) = {', '.join(ranks)}, #terms={len(p)}")

# SHARED GLOBAL: ∏(1 - s · G_i), s = var 200
print("\n--- Shared global ∏(1 - s·G_i) ---")
for n in range(1, 6):
    p = C(1)
    s = X(200)
    for i in range(n):
        gi = gadget(i)
        p = poly_mul(p, poly_add(C(1), poly_neg(poly_mul(s, gi))))
    
    all_vars = sorted(set().union(*(m for m in p.keys() if m)))
    nv = len(all_vars)
    vmap = {v: j for j, v in enumerate(all_vars)}
    p2 = {frozenset(vmap[v] for v in m): c for m, c in p.items()}
    
    ranks = []
    for k in [1, 2]:
        r = spdp_rank(p2, nv, k)
        ranks.append(str(r))
    print(f"  n={n}: vars={nv}, rank(κ=1,2) = {', '.join(ranks)}, #terms={len(p)}")

# MIXED: ∏_blocks (1 - ε_b · ∑_{block} G_i²)
print("\n--- Mixed: product of (1 - ε·∑G²) blocks ---")
for n in [4, 6]:
    for bs in [1, 2, n]:
        B = (n + bs - 1) // bs
        p = C(1)
        for b in range(B):
            block_sum = {}
            for i in range(b*bs, min((b+1)*bs, n)):
                gi = gadget(i)
                block_sum = poly_add(block_sum, poly_mul(gi, gi))
            eps = X(300 + b)
            p = poly_mul(p, poly_add(C(1), poly_neg(poly_mul(eps, block_sum))))
        
        all_vars = sorted(set().union(*(m for m in p.keys() if m)))
        nv = len(all_vars)
        vmap = {v: j for j, v in enumerate(all_vars)}
        p2 = {frozenset(vmap[v] for v in m): c for m, c in p.items()}
        
        ranks = []
        for k in [1, 2]:
            if k > nv: ranks.append("-"); continue
            t0 = time.time()
            r = spdp_rank(p2, nv, k)
            if time.time() - t0 > 10: ranks.append(f"{r}*"); break
            ranks.append(str(r))
        print(f"  n={n}, bs={bs}, B={B}: vars={nv}, rank(κ=1,2) = {', '.join(ranks)}")

print("\n" + "=" * 60)
print("ANALYSIS: Compare growth rates across forms")
print("=" * 60)
