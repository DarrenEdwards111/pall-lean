#!/usr/bin/env python3
"""
Bridge Stage 1 Test: Does a correct SAT solver's compiled polynomial
have nonzero traced Möbius mass at |T|=2?

Model: Sequential AND checker
- Content vars: x_1, ..., x_n (one per clause, representing clause satisfaction)
- State vars: s_0, ..., s_n (accumulator state)
- Transition: s_i = s_{i-1} * x_i (running AND)
- Output: s_n (1 iff all clauses satisfied)

Compiled as polynomial constraints:
  For each step i: (s_i - s_{i-1} * x_i)^2 = 0
  Output constraint: s_n must equal the SAT answer

The full compiled polynomial (sum of constraint squares):
  p = sum_i (s_i - s_{i-1} * x_i)^2

This is the "sum form" — it's a local sum where each piece
involves s_{i-1}, s_i, and x_i.

After partial trace (sum over all {0,1}^{n+1} assignments to s_0,...,s_n):
  partialTrace(p) = sum_{s} sum_i (s_i - s_{i-1} * x_i)^2
"""

import numpy as np
from itertools import product as cartesian_product
from collections import defaultdict
import sympy
from sympy import symbols, expand, Poly
from sympy.polys.monomials import itermonomials

def build_sequential_and_polynomial(n):
    """Build the compiled polynomial for sequential AND of n content vars.
    
    Content vars: x_1, ..., x_n
    State vars: s_0, s_1, ..., s_n
    
    Constraints: s_0 = 1 (initial state), s_i = s_{i-1} * x_i for i=1..n
    Polynomial: p = (s_0 - 1)^2 + sum_{i=1}^n (s_i - s_{i-1} * x_i)^2
    """
    x = [sympy.Symbol(f'x{i}') for i in range(n)]  # content vars
    s = [sympy.Symbol(f's{j}') for j in range(n + 1)]  # state vars
    
    # Constraint polynomial (sum of squares)
    p = (s[0] - 1)**2  # initial state = 1
    for i in range(n):
        p += (s[i+1] - s[i] * x[i])**2
    
    p = expand(p)
    return p, x, s

def partial_trace(p, state_vars):
    """Compute partial trace: sum over all {0,1} assignments to state vars."""
    result = sympy.Integer(0)
    n_state = len(state_vars)
    
    for assignment in cartesian_product([0, 1], repeat=n_state):
        subs = {state_vars[j]: assignment[j] for j in range(n_state)}
        result += p.subs(subs)
    
    return expand(result)

def compute_coeff_mass(p, var_set, all_content_vars):
    """Count nonzero-coefficient monomials supported entirely within var_set."""
    p_expanded = expand(p)
    if p_expanded == 0:
        return 0
    
    # Get all monomials with nonzero coefficients
    poly = Poly(p_expanded, *all_content_vars)
    count = 0
    for monom, coeff in poly.as_dict().items():
        if coeff != 0:
            # Check if monomial is supported within var_set
            supported_vars = {all_content_vars[i] for i, e in enumerate(monom) if e > 0}
            if supported_vars <= var_set:
                count += 1
    return count

def mobius_sign(S_card, T_card):
    """(-1)^|T\S| assuming S ⊆ T."""
    return (-1) ** (T_card - S_card)

def traced_mobius_obs(traced_p, T_indices, content_vars):
    """Compute traced Möbius observable for clause subset T."""
    T = set(T_indices)
    T_card = len(T)
    
    result = 0
    # Sum over all subsets S of T
    T_list = sorted(T)
    for r in range(T_card + 1):
        from itertools import combinations
        for S_tuple in combinations(T_list, r):
            S = set(S_tuple)
            S_card = len(S)
            
            # Variables for this subset
            var_set = {content_vars[i] for i in S}
            
            # Coefficient mass
            mass = compute_coeff_mass(traced_p, var_set, content_vars)
            
            # Möbius sign
            sign = mobius_sign(S_card, T_card)
            
            result += sign * mass
    
    return result

def run_experiment(n):
    """Test bridge Stage 1 for sequential AND of n content vars."""
    print(f"\n{'='*60}")
    print(f"Sequential AND checker, n={n} content vars")
    print(f"{'='*60}")
    
    p, x, s = build_sequential_and_polynomial(n)
    print(f"Compiled polynomial (before trace): {len(str(p))} chars")
    
    # Partial trace
    traced_p = partial_trace(p, s)
    print(f"After partial trace: {traced_p}")
    
    # Compute traced Möbius obs for all pairs (|T|=2)
    from itertools import combinations
    print(f"\nTraced Möbius observable at |T|=2:")
    total_mass = 0
    for pair in combinations(range(n), 2):
        obs = traced_mobius_obs(traced_p, pair, x)
        if obs != 0:
            print(f"  T={pair}: f̂_T = {obs}")
        total_mass += abs(obs)
    
    print(f"\nTotal |T|=2 mass: {total_mass}")
    
    if total_mass == 0:
        print("⚠️  ZERO pairwise mass — Stage 1 bridge FAILS for this model!")
    else:
        print("✅ Nonzero pairwise mass — Stage 1 bridge holds for this model")
    
    # Also check |T|=1 for reference
    print(f"\nTraced Möbius observable at |T|=1:")
    for i in range(n):
        obs = traced_mobius_obs(traced_p, [i], x)
        print(f"  T={{{i}}}: f̂_T = {obs}")
    
    return total_mass

# Run for small n
for n in [2, 3, 4]:
    run_experiment(n)
