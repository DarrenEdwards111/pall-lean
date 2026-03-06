#!/usr/bin/env python3
"""
Scale test: partial trace channel Möbius mass at |T|=2 for different models.
Does the separation grow with n?
"""
import numpy as np
from itertools import combinations, product as cart_product
from sympy import symbols, expand, Poly
from functools import reduce

def run(n_clauses):
    cs = 2  # clause size
    nc = n_clauses
    n_content = nc * cs
    n_state = nc
    
    xs = symbols(f'x0:{n_content}')
    ss = symbols(f's0:{n_state}')
    content_vars = list(xs)
    state_vars = list(ss)
    
    gates = []
    for i in range(nc):
        gates.append(xs[i*cs] * xs[i*cs+1])
    
    # Build models
    pure_product = reduce(lambda a,b: expand(a*b), [1 - g for g in gates])
    pure_sum = sum(gates)
    
    # TM violation (sum of squared constraints)
    c0 = ss[0] - gates[0]
    violations = [c0**2]
    for t in range(1, nc):
        ct = ss[t] - ss[t-1]*(1 - gates[t]) - gates[t]
        violations.append(expand(ct**2))
    tm_violation = expand(sum(violations))
    
    # TM product
    tm_product = reduce(lambda a,b: expand(a*b), [1 - v for v in violations])
    
    models = {
        'pure_product': pure_product,
        'pure_sum': pure_sum,
        'tm_violation': tm_violation,
        'tm_product': tm_product,
    }
    
    # Partial trace channel
    def partial_trace(poly):
        result = 0
        for bits in cart_product([0, 1], repeat=n_state):
            subs = {ss[i]: bits[i] for i in range(n_state)}
            result += poly.subs(subs)
        return expand(result)
    
    # Coeff mass helper
    def coeff_mass_content(poly, var_indices):
        subset_vars = [content_vars[i] for i in var_indices]
        other_vars = [v for i,v in enumerate(content_vars) if i not in var_indices]
        subs = {v: 0 for v in other_vars}
        restricted = expand(poly.subs(subs))
        if restricted == 0:
            return 0
        try:
            p = Poly(restricted, *subset_vars, domain='ZZ')
            return sum(abs(c) for c in p.as_dict().values())
        except:
            return abs(int(restricted)) if restricted != 0 else 0
    
    # Möbius at level 2 only
    def mobius_level2(poly):
        # f_S for |S|=0,1,2
        f = {}
        f[frozenset()] = coeff_mass_content(poly, [])
        for i in range(nc):
            idx = list(range(i*cs, (i+1)*cs))
            f[frozenset([i])] = coeff_mass_content(poly, idx)
        
        total_fhat2 = 0
        for i, j in combinations(range(nc), 2):
            idx_ij = list(range(i*cs, (i+1)*cs)) + list(range(j*cs, (j+1)*cs))
            f_ij = coeff_mass_content(poly, idx_ij)
            fhat = f_ij - f[frozenset([i])] - f[frozenset([j])] + f[frozenset()]
            total_fhat2 += abs(fhat)
        return total_fhat2
    
    print(f"\nn={nc}:")
    for name, poly in models.items():
        traced = partial_trace(poly)
        m2 = mobius_level2(traced)
        n_pairs = nc * (nc-1) // 2
        print(f"  {name:20s}: Möbius |T|=2 total mass = {int(m2):6d}  (C(n,2)={n_pairs})")

for n in [2, 3, 4, 5]:
    print(f"\n{'='*50}")
    try:
        run(n)
    except Exception as e:
        print(f"  ERROR at n={n}: {e}")
        break
