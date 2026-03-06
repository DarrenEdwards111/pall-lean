#!/usr/bin/env python3
"""
Fast numeric Markov channel test using truth-table representation.

Polynomial p over variables v_1..v_N is stored as a vector of 2^N coefficients
(multilinear extension). Operations are fast via numpy.

Partial trace over state vars = sum over {0,1}^m assignments to state vars.
"""
import numpy as np
from itertools import combinations, product as cart_product
from math import comb

def poly_to_vec(n_vars, eval_fn):
    """Build multilinear polynomial vector from evaluation on {0,1}^n.
    eval_fn(assignment) -> value, where assignment is tuple of 0/1."""
    size = 2**n_vars
    vals = np.zeros(size, dtype=np.float64)
    for i in range(size):
        bits = tuple((i >> j) & 1 for j in range(n_vars))
        vals[i] = eval_fn(bits)
    # Möbius transform: point values -> multilinear coefficients
    coeffs = vals.copy()
    for j in range(n_vars):
        step = 1 << j
        for i in range(size):
            if i & step:
                coeffs[i] -= coeffs[i ^ step]
    return coeffs

def coeff_mass_subset(coeffs, n_vars, var_indices):
    """Sum of |coeff| for monomials using only variables in var_indices."""
    mask = 0
    for v in var_indices:
        mask |= (1 << v)
    total = 0.0
    for i in range(len(coeffs)):
        # monomial i uses variable j iff bit j is set
        if (i & ~mask) == 0 and i != 0:  # only vars in subset, exclude constant
            total += abs(coeffs[i])
    return total

def mobius_level_k(coeffs, n_vars, clause_ranges, k):
    """Total Möbius mass at level k across all k-subsets of clauses."""
    nc = len(clause_ranges)
    
    # Compute f_S for needed subsets
    f_cache = {}
    
    def get_f(clause_set):
        key = frozenset(clause_set)
        if key not in f_cache:
            var_indices = []
            for c in clause_set:
                var_indices.extend(clause_ranges[c])
            f_cache[key] = coeff_mass_subset(coeffs, n_vars, var_indices)
        return f_cache[key]
    
    total = 0.0
    for T in combinations(range(nc), k):
        T_set = set(T)
        fhat = 0.0
        for r in range(k+1):
            for S in combinations(T, r):
                sign = (-1) ** (k - r)
                fhat += sign * get_f(S)
        total += abs(fhat)
    return total

def run_test(nc):
    cs = 2  # clause size (AND of 2 vars)
    n_content = nc * cs
    n_state = nc
    n_total = n_content + n_state
    
    # Gate i = x_{2i} AND x_{2i+1}
    def gate(bits, i):
        return bits[i*cs] * bits[i*cs+1]
    
    # === Models ===
    
    # Pure product: Π(1 - G_i)
    def pure_product(bits):
        val = 1.0
        for i in range(nc):
            val *= (1 - gate(bits, i))
        return val
    
    # Pure sum: Σ G_i
    def pure_sum(bits):
        return sum(gate(bits, i) for i in range(nc))
    
    # TM violation: Σ (constraint_t)^2 where constraints couple through state vars
    def tm_violation(bits):
        # s vars are bits[n_content:]
        g = [gate(bits, i) for i in range(nc)]
        s = [bits[n_content + t] for t in range(nc)]
        total = (s[0] - g[0])**2
        for t in range(1, nc):
            ct = s[t] - s[t-1]*(1 - g[t]) - g[t]
            total += ct**2
        return total
    
    # TM product: Π(1 - constraint_t^2)
    def tm_product(bits):
        g = [gate(bits, i) for i in range(nc)]
        s = [bits[n_content + t] for t in range(nc)]
        val = 1.0
        c0 = s[0] - g[0]
        val *= (1 - c0**2)
        for t in range(1, nc):
            ct = s[t] - s[t-1]*(1 - g[t]) - g[t]
            val *= (1 - ct**2)
        return val
    
    # === Partial trace channel ===
    # For models with state vars: sum p(x, s) over s ∈ {0,1}^m
    # Result is polynomial in content vars only
    
    def partial_trace_vec(model_fn):
        """Compute partial-traced polynomial as vector over content vars."""
        n_c = n_content
        size_c = 2**n_c
        traced_vals = np.zeros(size_c, dtype=np.float64)
        
        for ic in range(size_c):
            content_bits = tuple((ic >> j) & 1 for j in range(n_c))
            for is_ in range(2**n_state):
                state_bits = tuple((is_ >> j) & 1 for j in range(n_state))
                full_bits = content_bits + state_bits
                traced_vals[ic] += model_fn(full_bits)
        
        # Möbius transform to get coefficients
        coeffs = traced_vals.copy()
        for j in range(n_c):
            step = 1 << j
            for i in range(size_c):
                if i & step:
                    coeffs[i] -= coeffs[i ^ step]
        return coeffs
    
    # Content-only models: just build directly
    def content_vec(model_fn):
        return poly_to_vec(n_content, lambda bits: model_fn(bits + (0,)*n_state))
    
    clause_ranges = [list(range(i*cs, (i+1)*cs)) for i in range(nc)]
    
    print(f"\nn={nc}, content_vars={n_content}, state_vars={n_state}")
    print(f"  C(n,2)={comb(nc,2)}, C(n,3)={comb(nc,3)}")
    
    models_content = {
        'pure_product': lambda b: pure_product(b + (0,)*n_state),
        'pure_sum': lambda b: pure_sum(b + (0,)*n_state),
    }
    
    models_state = {
        'tm_violation': tm_violation,
        'tm_product': tm_product,
    }
    
    for name, fn in models_content.items():
        coeffs = poly_to_vec(n_content, fn)
        m2 = mobius_level_k(coeffs, n_content, clause_ranges, 2)
        m3 = mobius_level_k(coeffs, n_content, clause_ranges, 3) if nc >= 3 else 0
        print(f"  {name:20s} (no channel): |T|=2 mass={m2:8.0f}  |T|=3 mass={m3:8.0f}")
    
    for name, fn in models_state.items():
        coeffs = partial_trace_vec(fn)
        m2 = mobius_level_k(coeffs, n_content, clause_ranges, 2)
        m3 = mobius_level_k(coeffs, n_content, clause_ranges, 3) if nc >= 3 else 0
        print(f"  {name:20s} (partial tr): |T|=2 mass={m2:8.0f}  |T|=3 mass={m3:8.0f}")

for nc in [2, 3, 4, 5, 6, 7, 8]:
    try:
        run_test(nc)
    except MemoryError:
        print(f"  n={nc}: out of memory")
        break
