#!/usr/bin/env python3
"""
Möbius-transformed interaction observable.

Define clause-level observables f_S, then Möbius-invert:
  f_S(p) = SPDP-style statistic for clause subset S
  f̂_T = ∑_{S⊆T} (-1)^{|T\S|} f_S

Test whether:
  f̂_T is large for product verifier (NP)
  f̂_T is small for compiled sum (P)
  Correctness forces f̂_T to be large for any correct solver

Observable candidates:
A. f_S(p) = rank of derivative space restricted to variables in clauses S
B. f_S(p) = ∑_{monomials using only vars in S} |coeff|
C. f_S(p) = evaluation of κ-fold derivative at zero, using vars from S
D. f_S(p) = number of nonzero derivatives using one var per clause in S
"""
import numpy as np
from itertools import combinations, product as cartprod
from collections import defaultdict
from math import comb

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

# Clause structure: clause i uses vars {2i, 2i+1}
def clause_vars(i):
    return [2*i, 2*i+1]

def all_clause_vars(S):
    """Variables for a set of clause indices."""
    v = []
    for i in S:
        v.extend(clause_vars(i))
    return v

# === Observable A: rank restricted to clause subset ===
def obs_rank(p, S, kappa=1):
    """SPDP rank using only variables from clauses in S."""
    v = all_clause_vars(S)
    if len(v) < kappa: return 0
    return spdp_rank(p, v, kappa)

# === Observable B: coefficient mass on clause subset ===
def obs_coeff_mass(p, S):
    """Sum of |coeff| for monomials using only variables in clauses S."""
    allowed = set()
    for i in S: allowed.update(clause_vars(i))
    mass = 0
    for m, c in p.items():
        if all(v in allowed for v in m):
            mass += abs(c)
    return mass

# === Observable C: derivative at zero ===
def obs_deriv_zero(p, S):
    """∂_{one var per clause in S} p |_{x=0}, summed over all choices."""
    total = 0
    clause_list = list(S)
    var_choices = [clause_vars(i) for i in clause_list]
    
    for choice in cartprod(*var_choices):
        d = p
        for v in choice:
            d = pderiv(d, v)
            if not d: break
        if d:
            total += abs(d.get(frozenset(), 0))
    return total

# === Observable D: nonzero derivative count ===
def obs_nonzero_derivs(p, S):
    """Count of derivative choices (one var per clause in S) giving nonzero."""
    count = 0
    clause_list = list(S)
    var_choices = [clause_vars(i) for i in clause_list]
    
    for choice in cartprod(*var_choices):
        d = p
        for v in choice:
            d = pderiv(d, v)
            if not d: break
        if d: count += 1
    return count

# === Möbius inversion ===
def mobius_invert(f_values, T):
    """
    f̂_T = ∑_{S⊆T} (-1)^{|T\S|} f_S
    f_values: dict mapping frozenset(S) → value
    T: frozenset
    """
    T_list = sorted(T)
    result = 0
    for k in range(len(T_list)+1):
        for S in combinations(T_list, k):
            S_set = frozenset(S)
            sign = (-1)**(len(T) - k)
            result += sign * f_values.get(S_set, 0)
    return result


# === Build polynomials ===
def productPoly(n):
    """∏(1 - z_i·G_i), G_i = x_{2i}+x_{2i+1}"""
    p = C(1)
    for i in range(n):
        g = poly_add(X(2*i), X(2*i+1))
        p = poly_mul(p, poly_add(C(1), poly_neg(poly_mul(X(1000+i), g))))
    return p

def sumPoly(n):
    """∑(x_{2i}+x_{2i+1})²  [multilinear: x²→0, so ∑(2·x_{2i}·x_{2i+1})]"""
    p = {}
    for i in range(n):
        g = poly_add(X(2*i), X(2*i+1))
        p = poly_add(p, poly_mul(g, g))
    return p

def productSimple(n):
    """∏(1-x_{2i}·x_{2i+1}) — simpler product with AND gadgets"""
    p = C(1)
    for i in range(n):
        p = poly_mul(p, poly_add(C(1), poly_neg(poly_mul(X(2*i), X(2*i+1)))))
    return p

def sumSimple(n):
    """∑ x_{2i}·x_{2i+1} — sum of AND gadgets"""
    p = {}
    for i in range(n):
        p = poly_add(p, poly_mul(X(2*i), X(2*i+1)))
    return p


print("=" * 70)
print("MÖBIUS OBSERVABLE EXPERIMENTS")
print("=" * 70)

# Use simple gadgets G_i = x_{2i}·x_{2i+1} for cleaner algebra
print("\nUsing G_i = x_{2i}·x_{2i+1} (AND gadgets)")
print("Product: ∏(1-G_i),  Sum: ∑G_i")

for obs_name, obs_fn in [
    ("rank_1", lambda p, S: obs_rank(p, S, 1)),
    ("coeff_mass", obs_coeff_mass),
    ("deriv_zero", obs_deriv_zero),
    ("nonzero_derivs", obs_nonzero_derivs),
]:
    print(f"\n--- Observable: {obs_name} ---")
    
    for n in [3, 4, 5]:
        pp = productSimple(n)
        sp = sumSimple(n)
        
        clauses = list(range(n))
        
        # Compute f_S for all subsets S of size ≤ 3
        f_prod = {}
        f_sum = {}
        for size in range(n+1):
            for S in combinations(clauses, size):
                S_set = frozenset(S)
                f_prod[S_set] = obs_fn(pp, S)
                f_sum[S_set] = obs_fn(sp, S)
        
        # Möbius inversion for subsets of size 1, 2, 3
        print(f"\n  n={n}:")
        print(f"  {'|T|':>4} {'T':>12} {'f_prod':>8} {'f_sum':>8} {'f̂_prod':>8} {'f̂_sum':>8}")
        
        for size in [1, 2, 3]:
            if size > n: break
            for T in combinations(clauses, size):
                T_set = frozenset(T)
                fp = f_prod[T_set]
                fs = f_sum[T_set]
                fhat_p = mobius_invert(f_prod, T_set)
                fhat_s = mobius_invert(f_sum, T_set)
                T_str = '{' + ','.join(str(t) for t in T) + '}'
                print(f"  {size:>4} {T_str:>12} {fp:>8} {fs:>8} {fhat_p:>8} {fhat_s:>8}")

print("\n" + "=" * 70)
print("KEY: Look for an observable where:")
print("  f̂_T(product) is LARGE (growing with n)")
print("  f̂_T(sum) is ZERO or SMALL")
print("  This would be the Möbius-level separation.")
print("=" * 70)

# Summary statistics
print("\n--- Summary: Total |f̂| across all subsets of each size ---")
for n in [4, 5, 6]:
    pp = productSimple(n)
    sp = sumSimple(n)
    clauses = list(range(n))
    
    for obs_name, obs_fn in [("nonzero_derivs", obs_nonzero_derivs)]:
        f_prod = {}
        f_sum = {}
        for size in range(n+1):
            for S in combinations(clauses, size):
                S_set = frozenset(S)
                f_prod[S_set] = obs_fn(pp, S)
                f_sum[S_set] = obs_fn(sp, S)
        
        print(f"\n  n={n}, observable={obs_name}:")
        for size in range(1, min(n+1, 5)):
            total_fhat_p = 0
            total_fhat_s = 0
            for T in combinations(clauses, size):
                T_set = frozenset(T)
                total_fhat_p += abs(mobius_invert(f_prod, T_set))
                total_fhat_s += abs(mobius_invert(f_sum, T_set))
            print(f"    |T|={size}: ∑|f̂_prod|={total_fhat_p}  ∑|f̂_sum|={total_fhat_s}")
