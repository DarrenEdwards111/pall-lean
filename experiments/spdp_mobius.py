#!/usr/bin/env python3
"""
Möbius inversion as the bridge channel.

The Möbius function on the boolean lattice connects:
  g(S) = ∑_{T⊆S} f(T)  ⟺  f(S) = ∑_{T⊆S} (-1)^{|S\T|} g(T)

For clause satisfaction:
  sum form g = ∑ G_i (cumulative violations)
  product form f = ∏(1-G_i) (exact "all satisfied" indicator)

These are related by Möbius inversion on the subset lattice.

KEY IDEA: The fast Möbius transform decomposes into n "butterfly"
stages, each a rank-2 linear map. Track SPDP rank through each stage.
If rank grows slowly enough, maybe we can bound it.

Also test: Möbius on the CLAUSE lattice (partial order of clause subsets)
rather than the full variable lattice.
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

# === Fast Möbius Transform (butterfly decomposition) ===
# Starting from f_0 = 1 (constant), apply n butterflies:
# At stage k: f_k = f_{k-1} · (1 - G_k)
# = f_{k-1} - f_{k-1}·G_k
#
# This is just sequential multiplication by (1-G_k) factors.
# Track rank at each stage.

print("=" * 70)
print("MÖBIUS TRANSFORM — BUTTERFLY RANK TRACKING")
print("=" * 70)

print("\n--- Stage-by-stage rank of ∏_{i≤k}(1-G_i) ---")
print("G_i = x_{2i}·x_{2i+1} (AND gate, disjoint vars)")
print()
print(f"{'n':>3} {'stage':>6} {'#terms':>7} {'rank_1':>7} {'rank_2':>7} {'rank_3':>7}")

for n in [4, 5, 6, 7]:
    p = C(1)
    for k in range(n):
        g_k = poly_mul(X(2*k), X(2*k+1))
        p = poly_add(p, poly_neg(poly_mul(p, g_k)))  # p = p*(1-g_k)
        
        av = get_vars(p)
        r1 = spdp_rank(p, av, 1) if len(av)>=1 else 0
        r2 = spdp_rank(p, av, 2) if len(av)>=2 else 0
        r3 = spdp_rank(p, av, 3) if len(av)>=3 else 0
        
        print(f"{n:>3} {k+1:>6} {len(p):>7} {r1:>7} {r2:>7} {r3:>7}")
    print()

# === Reverse direction: from product, can Möbius recover sum? ===
# ∏(1-G_i) → ∑G_i via Möbius inversion
# If p = ∏(1-G_i), then log(p) = ∑ log(1-G_i) ≈ -∑G_i (for small G_i)
# Over integers: 1-p = ∑G_i - ∑_{i<j}G_iG_j + ... (inclusion-exclusion)
# First-order term: ∑G_i = 1 - p + higher order

print("--- Möbius layers: decompose ∏(1-G_i) into IE levels ---")
print("Level 0: constant 1")
print("Level 1: -∑G_i")
print("Level 2: +∑_{i<j} G_iG_j")
print("Level k: (-1)^k ∑_{|S|=k} ∏_{i∈S} G_i")
print()
print(f"{'n':>3} {'level':>6} {'#terms':>7} {'rank_1':>7} {'rank_2':>7}")

for n in [4, 5, 6]:
    for level in range(n+1):
        # Level k contribution: (-1)^k * ∑_{|S|=k} ∏_{i∈S} G_i
        layer = {}
        sign = (-1)**level
        for S in combinations(range(n), level):
            term = C(sign)
            for i in S:
                term = poly_mul(term, poly_mul(X(2*i), X(2*i+1)))
            layer = poly_add(layer, term)
        
        av = get_vars(layer)
        r1 = spdp_rank(layer, av, 1) if len(av)>=1 else 0
        r2 = spdp_rank(layer, av, 2) if len(av)>=2 else 0
        
        print(f"{n:>3} {level:>6} {len(layer):>7} {r1:>7} {r2:>7}")
    print()

# === KEY EXPERIMENT: Cumulative Möbius rank ===
# Build product incrementally, track rank of PARTIAL SUMS
# partial_k = ∑_{j=0}^{k} layer_j
# Does rank grow monotonically? Where does it jump?

print("--- Cumulative Möbius: rank of ∑_{j≤k} layer_j ---")
print(f"{'n':>3} {'layers':>7} {'#terms':>7} {'rank_1':>7} {'rank_2':>7}")

for n in [4, 5, 6, 7]:
    cumulative = {}
    for level in range(n+1):
        sign = (-1)**level
        for S in combinations(range(n), level):
            term = C(sign)
            for i in S:
                term = poly_mul(term, poly_mul(X(2*i), X(2*i+1)))
            cumulative = poly_add(cumulative, term)
        
        av = get_vars(cumulative)
        r1 = spdp_rank(cumulative, av, 1) if len(av)>=1 else 0
        r2 = spdp_rank(cumulative, av, 2) if len(av)>=2 else 0
        
        print(f"{n:>3} {level:>7} {len(cumulative):>7} {r1:>7} {r2:>7}")
    print()

# === Möbius on clause-variable bipartite graph ===
print("=" * 70)
print("MÖBIUS ON CLAUSE INTERACTION GRAPH")
print("=" * 70)
print("""
Instead of Möbius on the full lattice, consider Möbius on the
CLAUSE INTERACTION GRAPH:
- Nodes = clauses
- Edges = shared variables (for Tseitin on high-girth graph: NONE)

For disjoint clauses (high girth), Möbius on the clause graph is
trivial (each clause independent). The product factorizes as
∏(1-G_i) with no cross-clause interaction.

For TM compilation, clauses share variables through time steps.
The Möbius function on the TM's computation graph is more complex.

Key question: does the Möbius function of the computation graph
determine the SPDP rank?
""")

# Test: product of factors with SHARED vs DISJOINT variables
print("--- Shared vs disjoint factors and Möbius rank ---")
print()

# Disjoint: (1-x0x1)(1-x2x3)(1-x4x5)...
# Shared:   (1-x0x1)(1-x1x2)(1-x2x3)...  (chain, shared neighbors)

for n in [3, 4, 5, 6, 7]:
    # Disjoint
    pd = C(1)
    for i in range(n):
        pd = poly_mul(pd, poly_add(C(1), poly_neg(poly_mul(X(2*i), X(2*i+1)))))
    
    # Chain (shared)
    pc = C(1)
    for i in range(n):
        pc = poly_mul(pc, poly_add(C(1), poly_neg(poly_mul(X(i), X(i+1)))))
    
    dv = get_vars(pd)
    cv = get_vars(pc)
    
    dr2 = spdp_rank(pd, dv, 2) if len(dv)>=2 else 0
    cr2 = spdp_rank(pc, cv, 2) if len(cv)>=2 else 0
    
    print(f"  n={n}: disjoint_rank2={dr2}  chain_rank2={cr2}  (disjoint vars={len(dv)}, chain vars={len(cv)})")

print()
print("=" * 70)
print("Does shared-variable structure (chain/TM) reduce Möbius rank?")
print("If chain rank << disjoint rank, the computation graph matters!")
print("=" * 70)
