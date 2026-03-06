#!/usr/bin/env python3
"""
Critical question: Is the sequential accumulator a VALID compiled 
polynomial for AND?

The sequential accumulator computes AND correctly:
  s_0 = 1, s_i = s_{i-1} * x_i, output = s_n

But after partial trace, it becomes sum-form (local sum).
This means a correct solver CAN compile to sum-form.

Does this kill P≠NP via this framework? Not necessarily:
- The polynomial p = sum_i (s_i - s_{i-1}*x_i)^2 is the CONSTRAINT polynomial
- The actual computation is s_n = product of x_i
- The question is: what polynomial do we measure?

Key distinction:
1. CONSTRAINT polynomial: sum of squared violations (always sum-form)
2. OUTPUT polynomial: the function being computed (product-form for AND)
3. TRANSITION polynomial: the polynomial encoding the TM transitions

The SPDP framework measures the algebraic structure of the compiled 
polynomial, not the constraint polynomial.

Let's check: what IS the correct "compiled polynomial" for a TM?
In Tseitin encoding: product of (1 - violation_i) for each constraint.
This is PRODUCT form by definition.

But a poly-time TM can have poly(n) constraints → product of poly(n) 
terms → the degree is polynomial.

Wait — that's the point. The Tseitin polynomial is:
  Π_i (1 - G_i(x,s))
where G_i are the constraint gadgets.

For sequential AND:
  Π_{i=0}^n (1 - (s_i - s_{i-1}*x_i)^2)

This is PRODUCT FORM. Let me compute its traced Möbius mass.
"""

import sympy
from sympy import expand, Symbol
from itertools import combinations, product as cartesian_product

def partial_trace(p, state_vars):
    result = sympy.Integer(0)
    for assignment in cartesian_product([0, 1], repeat=len(state_vars)):
        subs = {state_vars[j]: assignment[j] for j in range(len(state_vars))}
        result += p.subs(subs)
    return expand(result)

def coeff_mass(p, var_set, all_vars):
    if p == 0:
        return 0
    from sympy import Poly
    poly = Poly(p, *all_vars)
    count = 0
    for monom, coeff in poly.as_dict().items():
        if coeff != 0:
            supported = {all_vars[i] for i, e in enumerate(monom) if e > 0}
            if supported <= var_set:
                count += 1
    return count

def mobius_obs(traced_p, T_indices, content_vars):
    T = sorted(T_indices)
    T_card = len(T)
    result = 0
    for r in range(T_card + 1):
        for S_tuple in combinations(T, r):
            S = set(S_tuple)
            var_set = {content_vars[i] for i in S}
            mass = coeff_mass(traced_p, var_set, content_vars)
            sign = (-1) ** (T_card - len(S))
            result += sign * mass
    return result

def test_product_form(n):
    """Tseitin-style PRODUCT of (1 - G_i) for sequential AND."""
    print(f"\n{'='*60}")
    print(f"PRODUCT FORM: Π(1 - G_i), sequential AND, n={n}")
    print(f"{'='*60}")
    
    x = [Symbol(f'x{i}') for i in range(n)]
    s = [Symbol(f's{j}') for j in range(n + 1)]
    
    # Product form: Π(1 - (s_i - s_{i-1}*x_i)^2) * (1 - (s_0 - 1)^2)
    p = (1 - (s[0] - 1)**2)
    for i in range(n):
        p *= (1 - (s[i+1] - s[i]*x[i])**2)
    
    p = expand(p)
    print(f"Product polynomial terms: {len(p.as_ordered_terms())}")
    
    traced = partial_trace(p, s)
    print(f"Traced polynomial: {traced}")
    
    # Check |T|=2 mass
    for pair in combinations(range(n), 2):
        obs = mobius_obs(traced, pair, x)
        if obs != 0:
            print(f"  |T|=2, T={pair}: f̂ = {obs}")
    
    total = sum(abs(mobius_obs(traced, pair, x)) for pair in combinations(range(n), 2))
    status = "✅ NONZERO" if total > 0 else "❌ ZERO"
    print(f"Total |T|=2 mass: {total} {status}")
    
    # Check all levels
    for k in range(1, n+1):
        level_mass = 0
        for T in combinations(range(n), k):
            obs = mobius_obs(traced, T, x)
            level_mass += abs(obs)
        print(f"  Level |T|={k} mass: {level_mass}")

def test_sum_form(n):
    """SUM of G_i (constraint violations) for sequential AND."""
    print(f"\n{'='*60}")
    print(f"SUM FORM: Σ G_i, sequential AND, n={n}")
    print(f"{'='*60}")
    
    x = [Symbol(f'x{i}') for i in range(n)]
    s = [Symbol(f's{j}') for j in range(n + 1)]
    
    p = (s[0] - 1)**2 + sum((s[i+1] - s[i]*x[i])**2 for i in range(n))
    p = expand(p)
    
    traced = partial_trace(p, s)
    print(f"Traced polynomial: {traced}")
    
    total = sum(abs(mobius_obs(traced, pair, x)) for pair in combinations(range(n), 2))
    status = "✅ NONZERO" if total > 0 else "❌ ZERO"
    print(f"Total |T|=2 mass: {total} {status}")

# Test both forms
for n in [2, 3]:
    test_product_form(n)
    test_sum_form(n)
