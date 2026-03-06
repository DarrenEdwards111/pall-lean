#!/usr/bin/env python3
"""
Test: Does a TM-compiled polynomial have nonzero Möbius coefficients f̂_T
at |T|≥2 when computation variables couple the clauses?

Model a TM that checks n clauses sequentially:
- State vars: q_t (time t)
- Content vars: x_{2i}, x_{2i+1} (clause i)
- Gate_t: transition from step t to t+1, involves q_t, q_{t+1}, and clause vars

The TM's state variables create INDIRECT coupling between clauses.
Does this coupling show up in the Möbius observable?
"""
import numpy as np
from itertools import combinations, product as cartprod
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

# === Observable functions ===
def obs_coeff_mass(p, clause_vars_set):
    """Sum of |coeff| for monomials using ONLY variables in the given set."""
    mass = 0
    for m, c in p.items():
        if all(v in clause_vars_set for v in m):
            mass += abs(c)
    return mass

def obs_coeff_mass_inclusive(p, clause_vars_set):
    """Sum of |coeff| for monomials that INCLUDE at least one var from each clause in set."""
    mass = 0
    for m, c in p.items():
        if m & clause_vars_set:  # monomial touches the clause vars
            mass += abs(c)
    return mass

def mobius_invert(f_values, T):
    T_list = sorted(T)
    result = 0
    for k in range(len(T_list)+1):
        for S in combinations(T_list, k):
            S_set = frozenset(S)
            sign = (-1)**(len(T) - k)
            result += sign * f_values.get(S_set, 0)
    return result

# === TM Compilation Models ===

def clause_content_vars(i):
    """Content variables for clause i: x_{2i}, x_{2i+1}"""
    return {2*i, 2*i+1}

def all_vars_for_clauses(clause_set):
    """All content variables for a set of clauses."""
    v = set()
    for i in clause_set:
        v.update(clause_content_vars(i))
    return v

# Model 1: Pure sum (no computation vars)
# P = ∑ G_i where G_i = x_{2i}·x_{2i+1}
def build_pure_sum(n):
    p = {}
    for i in range(n):
        p = poly_add(p, poly_mul(X(2*i), X(2*i+1)))
    return p

# Model 2: Pure product
# P = ∏(1 - G_i)
def build_pure_product(n):
    p = C(1)
    for i in range(n):
        p = poly_mul(p, poly_add(C(1), poly_neg(poly_mul(X(2*i), X(2*i+1)))))
    return p

# Model 3: TM with sequential state coupling
# Gate_t involves: q_t, q_{t+1}, x_{2t}, x_{2t+1}
# gate_t = q_t · x_{2t} · x_{2t+1} + q_t · q_{t+1}
# (checks clause t AND transitions state)
# P = ∑ gate_t  (sum form with coupled computation vars)
def build_tm_sum_coupled(n):
    p = {}
    for t in range(n):
        # Gate: q_t · (x_{2t} · x_{2t+1}) — clause check
        clause_check = poly_mul(X(1000+t), poly_mul(X(2*t), X(2*t+1)))
        # Transition: q_t · q_{t+1} — state coupling
        if t < n-1:
            transition = poly_mul(X(1000+t), X(1000+t+1))
            gate = poly_add(clause_check, transition)
        else:
            gate = clause_check
        p = poly_add(p, gate)
    return p

# Model 4: TM product form with state coupling
# P = ∏_t (1 - gate_t)
def build_tm_product_coupled(n):
    p = C(1)
    for t in range(n):
        clause_check = poly_mul(X(1000+t), poly_mul(X(2*t), X(2*t+1)))
        if t < n-1:
            transition = poly_mul(X(1000+t), X(1000+t+1))
            gate = poly_add(clause_check, transition)
        else:
            gate = clause_check
        p = poly_mul(p, poly_add(C(1), poly_neg(gate)))
    return p

# Model 5: TM sum with stronger coupling — state var appears in ALL gates
# gate_t = q_global · x_{2t} · x_{2t+1}
def build_tm_sum_global_state(n):
    p = {}
    for t in range(n):
        gate = poly_mul(X(9999), poly_mul(X(2*t), X(2*t+1)))
        p = poly_add(p, gate)
    return p

# Model 6: TM sum with pairwise coupling through accumulator
# acc_t = acc_{t-1} + G_t (accumulated check)
# gate_t = acc_t · G_t = (∑_{j≤t} G_j) · G_t
# This creates EXPLICIT pairwise coupling between clause t and all previous!
def build_tm_sum_accumulator(n):
    p = {}
    # Term for clause t coupled with clause j (j < t):
    # gate_{t,j} = G_j · G_t = x_{2j}·x_{2j+1}·x_{2t}·x_{2t+1}
    for t in range(n):
        for j in range(t):
            coupled = poly_mul(
                poly_mul(X(2*j), X(2*j+1)),
                poly_mul(X(2*t), X(2*t+1))
            )
            p = poly_add(p, coupled)
        # Also single clause term
        p = poly_add(p, poly_mul(X(2*t), X(2*t+1)))
    return p


print("=" * 70)
print("TM MÖBIUS OBSERVABLE TEST")
print("=" * 70)

models = [
    ("pure_sum", build_pure_sum),
    ("pure_prod", build_pure_product),
    ("tm_coupled", build_tm_sum_coupled),
    ("tm_global", build_tm_sum_global_state),
    ("tm_accum", build_tm_sum_accumulator),
]

for model_name, builder in models:
    print(f"\n--- Model: {model_name} ---")
    
    for n in [3, 4, 5]:
        p = builder(n)
        clauses = list(range(n))
        
        # Compute f_S using CONTENT variables only (clause vars)
        f_values = {}
        for size in range(n+1):
            for S in combinations(clauses, size):
                S_set = frozenset(S)
                content_vars = all_vars_for_clauses(S)
                f_values[S_set] = obs_coeff_mass(p, content_vars)
        
        # Möbius inversion
        print(f"\n  n={n}:")
        print(f"  {'|T|':>4} {'T':>10} {'f_S':>6} {'f̂_T':>6}")
        for size in [1, 2, 3]:
            if size > n: break
            for T in list(combinations(clauses, size))[:3]:  # show first 3
                T_set = frozenset(T)
                fS = f_values[T_set]
                fhat = mobius_invert(f_values, T_set)
                T_str = '{' + ','.join(str(t) for t in T) + '}'
                print(f"  {size:>4} {T_str:>10} {fS:>6} {fhat:>6}")

# Summary
print("\n" + "=" * 70)
print("SUMMARY: f̂_T at |T|=2 (first pair) for each model")
print("=" * 70)
print(f"{'n':>3} | ", end="")
for name, _ in models:
    print(f"{name:>12}", end="")
print()
print("-" * 68)

for n in [3, 4, 5, 6]:
    print(f"{n:>3} | ", end="")
    for model_name, builder in models:
        p = builder(n)
        clauses = list(range(n))
        f_values = {}
        for size in range(3):
            for S in combinations(clauses, size):
                S_set = frozenset(S)
                f_values[S_set] = obs_coeff_mass(p, all_vars_for_clauses(S))
        
        T_set = frozenset([0, 1])
        fhat = mobius_invert(f_values, T_set)
        print(f"{fhat:>12}", end="")
    print()

print()
print("KEY: If tm_coupled or tm_accum shows f̂_T ≠ 0 at |T|≥2,")
print("then computation coupling DOES force Möbius interaction!")
print("This would validate the bridge approach.")
