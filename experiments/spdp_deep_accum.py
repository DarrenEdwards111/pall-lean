#!/usr/bin/env python3
"""
Deep accumulator: push nonzero Möbius f̂_T to level 3 and beyond.

Level-2 accumulator: ∑_{j<t} G_j·G_t (pairwise coupling)
Level-3 accumulator: + ∑_{i<j<t} G_i·G_j·G_t (triple coupling)
Level-k accumulator: include all k-wise products

The full inclusion-exclusion (all levels) gives the product ∏(1-G_i).
Partial levels give intermediate objects.

Key question: how many levels does a correct SAT solver NEED?
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

def G(i):
    """Clause gadget: G_i = x_{2i}·x_{2i+1}"""
    return poly_mul(X(2*i), X(2*i+1))

def obs_coeff_mass(p, var_set):
    mass = 0
    for m, c in p.items():
        if all(v in var_set for v in m):
            mass += abs(c)
    return mass

def clause_vars(S):
    v = set()
    for i in S: v.update({2*i, 2*i+1})
    return v

def mobius_invert(f_values, T):
    T_list = sorted(T)
    result = 0
    for k in range(len(T_list)+1):
        for S in combinations(T_list, k):
            sign = (-1)**(len(T) - k)
            result += sign * f_values.get(frozenset(S), 0)
    return result

# === Accumulator at depth d ===
# depth-1: ∑ G_i (pure sum)
# depth-2: ∑ G_i + ∑_{i<j} G_i·G_j
# depth-3: + ∑_{i<j<k} G_i·G_j·G_k
# depth-n: = ∏(1+G_i) - 1 (full product minus 1)
# With alternating signs: depth-k of ∏(1-G_i)

def build_depth_accum(n, depth, signed=True):
    """
    Build ∑_{k=1}^{depth} (-1)^{k+1} · ∑_{|S|=k} ∏_{i∈S} G_i
    
    This is the partial inclusion-exclusion up to level `depth`.
    Full depth=n gives 1 - ∏(1-G_i).
    """
    p = {}
    for k in range(1, min(depth, n) + 1):
        sign = (-1)**(k+1) if signed else 1
        for S in combinations(range(n), k):
            term = C(sign)
            for i in S:
                term = poly_mul(term, G(i))
            p = poly_add(p, term)
    return p

def build_product(n):
    p = C(1)
    for i in range(n):
        p = poly_mul(p, poly_add(C(1), poly_neg(G(i))))
    return p

print("=" * 70)
print("DEEP ACCUMULATOR: Möbius f̂_T at each level")
print("=" * 70)

for n in [4, 5, 6]:
    print(f"\n{'='*50}")
    print(f"n = {n}")
    print(f"{'='*50}")
    
    clauses = list(range(n))
    
    # Test each depth
    for depth in range(1, n+1):
        p = build_depth_accum(n, depth)
        
        # Compute f_S for all subsets
        f_vals = {}
        for size in range(n+1):
            for S in combinations(clauses, size):
                f_vals[frozenset(S)] = obs_coeff_mass(p, clause_vars(S))
        
        # Compute f̂_T for representative subsets at each level
        fhat_by_level = {}
        for level in range(1, n+1):
            # Take first subset of this size
            T = frozenset(range(level))
            fhat = mobius_invert(f_vals, T)
            fhat_by_level[level] = fhat
        
        fhat_str = '  '.join(f'L{l}={fhat_by_level[l]:>3}' for l in range(1, min(n+1, 6)))
        print(f"  depth={depth}: {fhat_str}  #terms={len(p)}")
    
    # Also show pure product
    pp = build_product(n)
    f_vals_p = {}
    for size in range(n+1):
        for S in combinations(clauses, size):
            f_vals_p[frozenset(S)] = obs_coeff_mass(pp, clause_vars(S))
    fhat_p = {}
    for level in range(1, n+1):
        T = frozenset(range(level))
        fhat_p[level] = mobius_invert(f_vals_p, T)
    fhat_str = '  '.join(f'L{l}={fhat_p[l]:>3}' for l in range(1, min(n+1, 6)))
    print(f"  product: {fhat_str}  #terms={len(pp)}")

print("\n" + "=" * 70)
print("KEY PATTERN")
print("=" * 70)
print("""
depth-d accumulator has f̂_T ≠ 0 for |T| ≤ d, f̂_T = 0 for |T| > d.
Product (depth-n) has f̂_T = 1 for ALL |T|.

Question: what depth does a poly-time SAT solver require?
""")

# === THE CRITICAL TEST ===
# A correct solver needs depth ≥ ??? to determine satisfiability.
# For Tseitin on high-girth graph with n clauses:
# - depth 1 (linear): can count violations but can't determine satisfiability
# - depth 2 (pairwise): can detect pairwise interactions
# - depth log(n): ???
# - depth n: equivalent to full product (exponential terms)

print("=" * 70)
print("SOLVER DEPTH REQUIREMENT")
print("=" * 70)

# Test: at what depth does the accumulator become "equivalent" to the product
# on boolean inputs?
from itertools import product as cartprod

for n in [3, 4]:
    print(f"\nn={n}: Boolean function comparison")
    print(f"{'depth':>6} {'matches_product':>16} {'matches_sum':>12} {'#zeros':>8}")
    
    pp = build_product(n)
    ps = build_depth_accum(n, 1)  # pure sum
    
    for depth in range(1, n+1):
        pa = build_depth_accum(n, depth)
        
        match_prod = 0
        match_sum = 0
        zeros = 0
        total = 0
        
        for bits in cartprod([0,1], repeat=2*n):
            assignment = {j: bits[j] for j in range(2*n)}
            
            def eval_p(poly):
                val = 0
                for m, c in poly.items():
                    v = c
                    for var in m:
                        v *= assignment[var]
                    val += v
                return val
            
            va = eval_p(pa)
            vp = eval_p(pp)
            vs = eval_p(ps)
            total += 1
            
            if va == vp: match_prod += 1
            if va == vs: match_sum += 1
            if va == 0: zeros += 1
        
        print(f"{depth:>6} {match_prod:>16}/{total} {match_sum:>12}/{total} {zeros:>8}/{total}")

# === Möbius mass growth ===
print("\n" + "=" * 70)
print("TOTAL MÖBIUS MASS ∑|f̂_T| at each level")
print("=" * 70)
print("(This is what needs to be superpolynomial for the bridge)")

for n in [4, 5, 6, 7]:
    print(f"\nn={n}:")
    clauses = list(range(n))
    
    for depth in [1, 2, 3, n, 'prod']:
        if depth == 'prod':
            p = build_product(n)
            label = "product"
        else:
            if depth > n: continue
            p = build_depth_accum(n, depth)
            label = f"depth-{depth}"
        
        f_vals = {}
        for size in range(n+1):
            for S in combinations(clauses, size):
                f_vals[frozenset(S)] = obs_coeff_mass(p, clause_vars(S))
        
        masses = []
        for level in range(1, n+1):
            total_mass = 0
            for T in combinations(clauses, level):
                total_mass += abs(mobius_invert(f_vals, frozenset(T)))
            masses.append(total_mass)
        
        mass_str = '  '.join(f'L{l+1}:{masses[l]:>4}' for l in range(min(n, 5)))
        print(f"  {label:>10}: {mass_str}")
