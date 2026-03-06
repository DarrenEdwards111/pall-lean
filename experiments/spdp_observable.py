#!/usr/bin/env python3
"""
Observable tensor channel T_k(p)[i1,...,ik] = ∂_{i1}...∂_{ik} p |_{x=0}

For multilinear polynomials, this equals the coefficient of x_{i1}·...·x_{ik}.

Test: does this invariant separate P from NP in a way that
the correctness of the solver FORCES high observable size?
"""
import numpy as np
from itertools import combinations
from collections import defaultdict

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

def eval_zero(p):
    """Evaluate polynomial at x=0 (constant term)."""
    return p.get(frozenset(), 0)

def pderiv(p,v):
    r=defaultdict(int)
    for m,c in p.items():
        if v in m: r[m-{v}]+=c
    return {m:c for m,c in r.items() if c}

def observable_tensor_entry(p, var_list):
    """T_k(p)[i1,...,ik] = ∂_{i1}...∂_{ik} p |_{x=0}"""
    d = p
    for v in var_list:
        d = pderiv(d, v)
        if not d: return 0
    return eval_zero(d)

def observable_size(p, variables, k):
    """Count nonzero entries in T_k."""
    count = 0
    total = 0
    for combo in combinations(variables, k):
        total += 1
        if observable_tensor_entry(p, combo) != 0:
            count += 1
    return count, total

def observable_rank(p, variables, k):
    """Rank of the flattened observable tensor (as a matrix)."""
    # Collect all k-derivatives evaluated at 0
    entries = []
    for combo in combinations(variables, k):
        d = p
        for v in combo:
            d = pderiv(d, v)
            if not d: break
        if d:
            entries.append((combo, eval_zero(d), d))
    
    # Also compute the FULL derivative vectors (not just at 0)
    derivs = [d for _, _, d in entries if d]
    if not derivs: return 0, 0
    
    all_m = sorted(set().union(*(d.keys() for d in derivs)),
                   key=lambda s:(len(s),tuple(sorted(s))))
    mi = {m:i for i,m in enumerate(all_m)}
    mat = np.zeros((len(derivs), len(all_m)))
    for i,d in enumerate(derivs):
        for m,c in d.items(): mat[i,mi[m]]=c
    
    full_rank = int(np.linalg.matrix_rank(mat))
    scalar_nonzero = sum(1 for _,v,_ in entries if v != 0)
    
    return full_rank, scalar_nonzero

# === Builders ===
def build_product(n):
    """∏(1-z_i·(x_{2i}+x_{2i+1}))"""
    p = C(1)
    for i in range(n):
        g = poly_add(X(2*i), X(2*i+1))
        p = poly_mul(p, poly_add(C(1), poly_neg(poly_mul(X(1000+i), g))))
    vars_all = list(range(2*n)) + list(range(1000,1000+n))
    return p, sorted(vars_all)

def build_sum(n):
    """∑(x_{2i}+x_{2i+1})²"""
    p = {}
    for i in range(n):
        g = poly_add(X(2*i), X(2*i+1))
        p = poly_add(p, poly_mul(g, g))
    return p, list(range(2*n))

def build_sum_with_z(n):
    """∑(1 - z_i·G_i)² = ∑(1 - 2z_iG_i + z_i²G_i²)
    Same z-variables as product, but summed not multiplied."""
    p = {}
    for i in range(n):
        g = poly_add(X(2*i), X(2*i+1))
        factor = poly_add(C(1), poly_neg(poly_mul(X(1000+i), g)))
        p = poly_add(p, poly_mul(factor, factor))
    vars_all = list(range(2*n)) + list(range(1000,1000+n))
    return p, sorted(vars_all)

print("=" * 70)
print("OBSERVABLE TENSOR EXPERIMENTS")
print("=" * 70)

# Test 1: Observable size (nonzero T_k entries)
print("\n--- T_k nonzero count: product vs sum vs sum_with_z ---")
print(f"{'n':>3} {'k':>3} {'prod_nz':>8} {'sum_nz':>8} {'sumZ_nz':>8} {'total':>8}")
for n in range(2, 7):
    for k in [1, 2, 3]:
        pp, pv = build_product(n)
        sp, sv = build_sum(n)
        szp, szv = build_sum_with_z(n)
        
        pnz, pt = observable_size(pp, pv, k)
        snz, st = observable_size(sp, sv, k)
        sznz, szt = observable_size(szp, szv, k)
        
        print(f"{n:>3} {k:>3} {pnz:>8} {snz:>8} {sznz:>8} {pt:>8}")

# Test 2: Full derivative rank vs scalar observable
print("\n--- Full rank vs scalar nonzero (k=2) ---")
print(f"{'n':>3} {'prod_rank':>10} {'prod_nz':>8} {'sum_rank':>10} {'sum_nz':>8} {'sumZ_rank':>10} {'sumZ_nz':>8}")
for n in range(2, 7):
    pp, pv = build_product(n)
    sp, sv = build_sum(n)
    szp, szv = build_sum_with_z(n)
    
    pr, pnz = observable_rank(pp, pv, 2)
    sr, snz = observable_rank(sp, sv, 2)
    szr, sznz = observable_rank(szp, szv, 2)
    
    print(f"{n:>3} {pr:>10} {pnz:>8} {sr:>10} {snz:>8} {szr:>10} {sznz:>8}")

# Test 3: THE CRITICAL TEST
# Both product and sum-with-z use the SAME variables (z_i and x_j).
# They compute "related" boolean functions.
# Product: = 0 iff any clause unsatisfied AND z_C chosen correctly
# Sum-with-z: = 0 iff all (1-z_C·G_C) = 0, i.e., z_C = 1/G_C for all C
#
# Key: can a poly-time TM produce a polynomial with the SAME z_i, x_j vars
# that has low observable size but correctly encodes SAT?
print("\n--- CRITICAL: Same variables, different observable sizes ---")
print("\nProduct ∏(1-z·G) and Sum ∑(1-z·G)² use SAME variables.")
print("Product has high T_k, Sum has low T_k.")
print("Both 'encode' clause satisfaction via z_i and x_j.\n")

for n in [3, 4, 5]:
    pp, pv = build_product(n)
    szp, szv = build_sum_with_z(n)
    
    # Observable at k=2 using only z-variables
    z_vars = list(range(1000, 1000+n))
    
    pnz_z, pt_z = observable_size(pp, z_vars, 2)
    snz_z, st_z = observable_size(szp, z_vars, 2)
    
    # Observable at k=2 using only x-variables  
    x_vars = list(range(2*n))
    pnz_x, pt_x = observable_size(pp, x_vars, 2)
    snz_x, st_x = observable_size(szp, x_vars, 2)
    
    # Mixed: one z, one x
    mixed_count_p = 0
    mixed_count_s = 0
    mixed_total = 0
    for zi in z_vars:
        for xi in x_vars:
            mixed_total += 1
            if observable_tensor_entry(pp, [zi, xi]) != 0:
                mixed_count_p += 1
            if observable_tensor_entry(szp, [zi, xi]) != 0:
                mixed_count_s += 1
    
    print(f"n={n}:")
    print(f"  T_2(z,z):  prod={pnz_z}/{pt_z}  sum={snz_z}/{st_z}")
    print(f"  T_2(x,x):  prod={pnz_x}/{pt_x}  sum={snz_x}/{st_x}")
    print(f"  T_2(z,x):  prod={mixed_count_p}/{mixed_total}  sum={mixed_count_s}/{mixed_total}")

# Test 4: Does the observable tensor at x=0 actually capture
# something about SATISFIABILITY?
print("\n--- Test 4: Observable tensor values ---")
print("Showing actual T_2 values for n=3 product (z-vars only)")
pp, _ = build_product(3)
z_vars = [1000, 1001, 1002]
for i, zi in enumerate(z_vars):
    for j, zj in enumerate(z_vars):
        if i < j:
            val = observable_tensor_entry(pp, [zi, zj])
            print(f"  T_2[z_{i}, z_{j}] = {val}")

print("\nSame for sum-with-z:")
szp, _ = build_sum_with_z(3)
for i, zi in enumerate(z_vars):
    for j, zj in enumerate(z_vars):
        if i < j:
            val = observable_tensor_entry(szp, [zi, zj])
            print(f"  T_2[z_{i}, z_{j}] = {val}")

print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)
print("""
Observable tensor T_k evaluated at x=0 gives the coefficient
of the degree-k monomial x_{i1}·...·x_{ik}.

Product form: many nonzero coefficients (cross-terms from expansion)
Sum form: few nonzero coefficients (locality of each term)

This is EXACTLY the same information as SPDP rank, just viewed
differently. The coefficient tensor IS the derivative space.

The channel C_k: p → T_k(p) is a LINEAR MAP.
Any linear map preserves the sum/product structure distinction.
No linear channel can bridge the gap because:
- Linear maps can't increase rank
- The sum form has low rank in any linear observable
- The product form has high rank in any linear observable

For a bridge, we might need a NONLINEAR channel.
Something that uses the BOOLEAN STRUCTURE (x²=x) or
evaluates at specific points, not just at x=0.
""")
