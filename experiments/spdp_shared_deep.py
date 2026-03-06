#!/usr/bin/env python3
"""
Deep dive: shared variables and their effect on SPDP rank.
Key finding: single shared variable kills rank to O(1).
Question: can we use this to build a compiler with poly rank in product form?
"""
import numpy as np
from itertools import combinations
from collections import defaultdict

def poly_mul(p1, p2):
    result = defaultdict(int)
    for m1, c1 in p1.items():
        for m2, c2 in p2.items():
            if m1 & m2: continue
            result[m1 | m2] += c1 * c2
    return {m: c for m, c in result.items() if c != 0}

def poly_add(p1, p2):
    result = defaultdict(int)
    for m, c in p1.items(): result[m] += c
    for m, c in p2.items(): result[m] += c
    return {m: c for m, c in result.items() if c != 0}

def poly_neg(p): return {m: -c for m, c in p.items()}
def X(i): return {frozenset([i]): 1}
def C(c): return {frozenset(): c} if c else {}

def pderiv(p, v):
    result = defaultdict(int)
    for m, c in p.items():
        if v in m: result[m - {v}] += c
    return {m: c for m, c in result.items() if c != 0}

def spdp_rank(poly, all_vars, kappa):
    derivs = []
    var_list = sorted(all_vars)
    for combo in combinations(range(len(var_list)), kappa):
        d = poly
        for idx in combo:
            d = pderiv(d, var_list[idx])
            if not d: break
        if d: derivs.append(d)
    if not derivs: return 0
    all_m = sorted(set().union(*(d.keys() for d in derivs)), key=lambda s: (len(s), tuple(sorted(s))))
    mi = {m: i for i, m in enumerate(all_m)}
    mat = np.zeros((len(derivs), len(all_m)))
    for i, d in enumerate(derivs):
        for m, c in d.items(): mat[i, mi[m]] = c
    return int(np.linalg.matrix_rank(mat))

def get_all_vars(p):
    v = set()
    for m in p.keys(): v |= m
    return v

# Experiment: k shared variables, n disjoint factors
# ∏_i (1 - s_1·s_2·...·s_k · x_i)
print("=" * 60)
print("Effect of # shared variables on product rank")
print("=" * 60)

print("\n--- ∏(1 - s₁·...·sₖ · x_i), varying k (shared) and n (factors) ---")
print(f"{'n':>4} {'k_shared':>8} {'κ=1':>6} {'κ=2':>6} {'κ=3':>6}")
for n in [3, 4, 5, 6]:
    for k in [0, 1, 2]:
        p = C(1)
        for i in range(n):
            # shared vars: 1000..1000+k-1, private var: i
            term_inner = X(i)
            for s in range(k):
                term_inner = poly_mul(term_inner, X(1000 + s))
            factor = poly_add(C(1), poly_neg(term_inner))
            p = poly_mul(p, factor)
        
        av = get_all_vars(p)
        ranks = []
        for kappa in [1, 2, 3]:
            if kappa > len(av):
                ranks.append("-")
            else:
                ranks.append(str(spdp_rank(p, av, kappa)))
        print(f"{n:>4} {k:>8} {ranks[0]:>6} {ranks[1]:>6} {ranks[2]:>6}")

# KEY EXPERIMENT: Can a TM compiler use shared variables?
# A TM has state variables that appear in EVERY gate.
# Model: ∏_t (1 - q · f_t(x_t)) where q is the "accepting state" indicator
print("\n" + "=" * 60)
print("TM-style: shared state variable q in every gate")
print("∏_t (1 - q · x_t)")
print("=" * 60)
print(f"{'n':>4} {'κ=1':>6} {'κ=2':>6} {'κ=3':>6}   vs disjoint ∏(1-x_i)")
for n in range(2, 8):
    # Shared q version
    q = X(999)
    p_shared = C(1)
    for i in range(n):
        p_shared = poly_mul(p_shared, poly_add(C(1), poly_neg(poly_mul(q, X(i)))))
    
    # Disjoint version (2 vars per factor)
    p_disj = C(1)
    for i in range(n):
        p_disj = poly_mul(p_disj, poly_add(C(1), poly_neg(poly_mul(X(500+i), X(i)))))
    
    av_s = get_all_vars(p_shared)
    av_d = get_all_vars(p_disj)
    
    r_s = [spdp_rank(p_shared, av_s, k) for k in [1,2,3] if k <= len(av_s)]
    r_d = [spdp_rank(p_disj, av_d, k) for k in [1,2,3] if k <= len(av_d)]
    
    while len(r_s) < 3: r_s.append(0)
    while len(r_d) < 3: r_d.append(0)
    
    print(f"{n:>4} {r_s[0]:>6} {r_s[1]:>6} {r_s[2]:>6}   disj: {r_d[0]:>4} {r_d[1]:>4} {r_d[2]:>4}")

# CRITICAL: What if the compiler polynomial is ∏(1 - q_t · G_t)
# where q_t are FRESH state indicators per time step?
# Then it's the disjoint product = superpoly rank (bad for P-side).
# But if q is SHARED (same accepting state)... rank stays low!
print("\n" + "=" * 60)
print("KEY INSIGHT: If TM compilation shares a global 'accept' variable")
print("across all gate checks, the product form has bounded rank.")
print("This would make the P-side collapse work IN PRODUCT FORM.")
print("But then: can the NP-side Tseitin product be extracted?")
print("Tseitin has INDEPENDENT z_C per clause = disjoint = superpoly rank.")
print("=" * 60)

# Test extraction: from ∏(1-q·x_i) can we extract ∏(1-z_i·x_i)?
# By specializing q → z_i for each factor? No — q is the SAME variable.
# The rank of ∏(1-q·x_i) is O(1) at κ≥2.
# The rank of ∏(1-z_i·x_i) is C(n,κ).
# So extraction CANNOT work: you can't extract high rank from low rank.
print("\nVerification: rank(∏(1-q·x_i)) vs rank(∏(1-z_i·x_i)) at κ=2")
for n in range(2, 7):
    q = X(999)
    p_shared = C(1)
    p_indep = C(1)
    for i in range(n):
        p_shared = poly_mul(p_shared, poly_add(C(1), poly_neg(poly_mul(q, X(i)))))
        p_indep = poly_mul(p_indep, poly_add(C(1), poly_neg(poly_mul(X(500+i), X(i)))))
    
    r_s = spdp_rank(p_shared, get_all_vars(p_shared), 2)
    r_i = spdp_rank(p_indep, get_all_vars(p_indep), 2)
    print(f"  n={n}: shared={r_s}, independent={r_i}")

print("\n" + "=" * 60)
print("CONCLUSION: Shared variables suppress rank (good for P-side)")
print("but also make extraction impossible (bad for bridge).")
print("The product-sum tension manifests here as shared-independent tension.")
print("=" * 60)
