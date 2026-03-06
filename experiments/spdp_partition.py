#!/usr/bin/env python3
"""
Quick test: how does block partition affect SPDP rank?
Pick FIRST var from each block (not all combos) for speed.
"""
import numpy as np
from itertools import combinations
from collections import defaultdict

def poly_mul(p1, p2):
    r = defaultdict(int)
    for m1, c1 in p1.items():
        for m2, c2 in p2.items():
            if m1 & m2: continue
            r[m1|m2] += c1*c2
    return {m:c for m,c in r.items() if c}

def poly_add(p1, p2):
    r = defaultdict(int)
    for m,c in p1.items(): r[m]+=c
    for m,c in p2.items(): r[m]+=c
    return {m:c for m,c in r.items() if c}

def poly_neg(p): return {m:-c for m,c in p.items()}
def X(i): return {frozenset([i]):1}
def C(c): return {frozenset():c} if c else {}

def pderiv(p,v):
    r = defaultdict(int)
    for m,c in p.items():
        if v in m: r[m-{v}]+=c
    return {m:c for m,c in r.items() if c}

def blocked_rank_fast(poly, partition, kappa):
    """Pick first var from each block, take kappa-subset of blocks."""
    reps = [blk[0] for blk in partition]
    derivs = []
    for combo in combinations(range(len(reps)), kappa):
        d = poly
        for bi in combo:
            d = pderiv(d, reps[bi])
            if not d: break
        if d: derivs.append(d)
    if not derivs: return 0
    all_m = sorted(set().union(*(d.keys() for d in derivs)), key=lambda s:(len(s),tuple(sorted(s))))
    mi = {m:i for i,m in enumerate(all_m)}
    mat = np.zeros((len(derivs),len(all_m)))
    for i,d in enumerate(derivs):
        for m,c in d.items(): mat[i,mi[m]]=c
    return int(np.linalg.matrix_rank(mat))

def full_rank(poly, n_vars, kappa):
    variables = sorted(set().union(*(m for m in poly.keys() if m)))
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

# Build: ∏(1 - z_i · (x_{2i}+x_{2i+1}))
def build(n):
    p = C(1)
    for i in range(n):
        z = X(1000+i)
        g = poly_add(X(2*i), X(2*i+1))
        p = poly_mul(p, poly_add(C(1), poly_neg(poly_mul(z, g))))
    return p

print("PARTITION EFFECT ON SPDP RANK (using z-var representatives)")
print("=" * 65)
print(f"{'n':>3} {'full':>6} {'n blk':>6} {'n/2':>6} {'2 blk':>6} {'1 blk':>6}  (κ=2)")

for n in range(2, 9):
    p = build(n)
    
    # Use z-variables as block reps
    # n blocks: z_0,...,z_{n-1}
    part_n = [[1000+i] for i in range(n)]
    
    # n/2 blocks: pair up
    part_half = []
    for i in range(0, n, 2):
        blk = [1000+i]
        if i+1 < n: blk.append(1000+i+1)
        part_half.append(blk)
    
    # 2 blocks
    h = n//2
    part_2 = [[1000+i for i in range(h)], [1000+i for i in range(h, n)]]
    
    # 1 block
    part_1 = [[1000+i for i in range(n)]]
    
    fr = full_rank(p, 0, 2)
    rn = blocked_rank_fast(p, part_n, 2)
    rh = blocked_rank_fast(p, part_half, 2)
    r2 = blocked_rank_fast(p, part_2, 2)
    r1 = blocked_rank_fast(p, part_1, 2)
    
    print(f"{n:>3} {fr:>6} {rn:>6} {rh:>6} {r2:>6} {r1:>6}")

print()
print("Now κ=3:")
print(f"{'n':>3} {'full':>6} {'n blk':>6} {'n/2':>6} {'2 blk':>6}  (κ=3)")
for n in range(3, 8):
    p = build(n)
    part_n = [[1000+i] for i in range(n)]
    part_half = []
    for i in range(0, n, 2):
        blk = [1000+i]
        if i+1 < n: blk.append(1000+i+1)
        part_half.append(blk)
    h = n//2
    part_2 = [[1000+i for i in range(h)], [1000+i for i in range(h, n)]]
    
    fr = full_rank(p, 0, 3)
    rn = blocked_rank_fast(p, part_n, 3)
    rh = blocked_rank_fast(p, part_half, 3)
    r2 = 0  # only 2 blocks, can't pick 3
    
    print(f"{n:>3} {fr:>6} {rn:>6} {rh:>6} {r2:>6}")

print()
print("KEY: As partition coarsens (fewer blocks), blocked rank drops.")
print("With B blocks, κ=2 gives at most C(B,2) derivatives.")
print("A poly-time TM with O(n) gates = O(n) blocks → C(n,2) = superpoly.")
print()
print("The ONLY way to get poly blocked rank: O(1) or O(log n) blocks.")
print("But a TM with poly(n) steps CAN'T be compressed to O(log n) blocks")
print("while keeping each block O(1) width.")
print()
print("UNLESS the Markov bridge provides a RE-BLOCKING that:")
print("1. Merges many TM steps into few blocks")
print("2. Each merged block still has bounded 'effective width'")
print("3. The blocked rank w.r.t. merged partition is polynomial")
print()
print("This is essentially a COMPRESSION of the computation.")
print("A poly-time TM has Kolmogorov complexity O(1) (fixed program).")
print("Could the Markov bridge use this compression?")
