#!/usr/bin/env python3
"""
Bridge test with multiple solver models:

1. Sequential AND (accumulator): s_i = s_{i-1} * x_i
2. Parallel AND (direct product): output = x_1 * x_2 * ... * x_n  
3. Tree AND: binary tree of multiplications
4. Counter model: count satisfied clauses, compare to n
5. Polynomial that explicitly computes AND correctly

The question: can ANY correct solver produce nonzero |T|=2 traced mass?
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

def test_model(name, p, content_vars, state_vars):
    n = len(content_vars)
    print(f"\n{'='*60}")
    print(f"Model: {name}, n={n}")
    
    traced_p = partial_trace(p, state_vars)
    print(f"Traced polynomial: {traced_p}")
    
    total_mass_2 = 0
    for pair in combinations(range(n), 2):
        obs = mobius_obs(traced_p, pair, content_vars)
        if obs != 0:
            print(f"  |T|=2, T={pair}: f̂ = {obs}")
        total_mass_2 += abs(obs)
    
    status = "✅ NONZERO" if total_mass_2 > 0 else "❌ ZERO"
    print(f"|T|=2 mass: {total_mass_2} {status}")
    return total_mass_2

n = 3
x = [Symbol(f'x{i}') for i in range(n)]

# Model 1: Sequential accumulator (already tested)
s = [Symbol(f's{j}') for j in range(n + 1)]
p1 = (s[0] - 1)**2 + sum((s[i+1] - s[i]*x[i])**2 for i in range(n))
test_model("Sequential AND (accumulator)", p1, x, s)

# Model 2: Direct product — no state vars at all
# p = (1 - x_0*x_1*x_2)^2 — this IS the AND function as a polynomial
# No state vars → partial trace is identity
p2 = (1 - x[0]*x[1]*x[2])**2
test_model("Direct product (no state)", expand(p2), x, [])

# Model 3: Tree AND with intermediate state
# t_01 = x_0 * x_1, then out = t_01 * x_2
t = [Symbol(f't{j}') for j in range(2)]
p3 = (t[0] - x[0]*x[1])**2 + (t[1] - t[0]*x[2])**2
test_model("Tree AND (intermediate state)", expand(p3), x, t)

# Model 4: Each state bit directly copies a content var, then AND the states
# s_i = x_i, out = s_0 * s_1 * s_2
s2 = [Symbol(f'u{j}') for j in range(n)]
p4 = sum((s2[i] - x[i])**2 for i in range(n)) + (1 - s2[0]*s2[1]*s2[2])**2
test_model("Copy+AND (state copies content)", expand(p4), x, s2)

# Model 5: Constraint-based — each pair of clauses has a consistency check
# This models a solver that explicitly checks pairs
v = [Symbol(f'v{j}') for j in range(3)]  # v_01, v_02, v_12 = pairwise ANDs
p5 = (v[0] - x[0]*x[1])**2 + (v[1] - x[0]*x[2])**2 + (v[2] - x[1]*x[2])**2
# Plus: output = v_01 * x_2 (or equivalently v_02 * x_1, etc.)
w = Symbol('w')
p5 += (w - v[0]*x[2])**2
test_model("Pairwise consistency checker", expand(p5), x, v + [w])

# Model 6: "Multiplication table" — directly encode x_0*x_1, x_0*x_2, etc.
# then verify consistency
# Just the raw product polynomial with no state at all
p6 = x[0]*x[1]*x[2]  # The AND function itself
test_model("Raw AND polynomial (no constraints)", expand(p6), x, [])

# Model 7: TM-like coupled constraints with content-content cross terms
# (s_1 - x_0*x_1)^2 forces s_1 = x_0*x_1
# Then (s_2 - s_1*x_2)^2 forces s_2 = x_0*x_1*x_2
# The cross term x_0*x_1 in the constraint creates content coupling
s3 = [Symbol(f'q{j}') for j in range(2)]
p7 = (s3[0] - x[0]*x[1])**2 + (s3[1] - s3[0]*x[2])**2
test_model("Content-coupled accumulator", expand(p7), x, s3)

print("\n" + "="*60)
print("SUMMARY")
print("="*60)
print("""
Key insight: The partial trace DESTROYS content coupling mediated
through state variables. After summing over {0,1}^m state assignments,
cross-terms like s*x_0*x_1 become:
  sum_{s=0,1} s*x_0*x_1 = 0*x_0*x_1 + 1*x_0*x_1 = x_0*x_1

But the SQUARED constraint (s - x_0*x_1)^2 = s^2 - 2s*x_0*x_1 + x_0^2*x_1^2
After trace: sum_{s=0,1} (s^2 - 2s*x_0*x_1 + x_0^2*x_1^2)
           = (0+1) - 2(0+1)*x_0*x_1 + 2*x_0^2*x_1^2
           = 1 - 2*x_0*x_1 + 2*x_0^2*x_1^2

This HAS cross terms! The question is whether the Möbius inversion
kills them.
""")
