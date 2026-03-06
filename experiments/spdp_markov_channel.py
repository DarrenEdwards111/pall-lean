#!/usr/bin/env python3
"""
Universal Markov Channel Bridge for SPDP
=========================================

Idea: Build a linear "coarse-graining" channel that:
1. Takes the full polynomial (content + computation variables)
2. Marginalizes out computation variables via partial trace
3. Preserves the EFFECT of computation-variable coupling on content interactions
4. Measures the resulting Möbius interaction structure

This is inspired by Darren's refinement channel from the quantum paper:
  - Raw subspace overlap: S_min = 0 (useless)
  - Coarse-grained (partial trace): S_coarse = 2.0 (55,000x improvement)

The same principle: fine-grained observation loses signal, but coarse-graining
over the "new" (computation) variables reveals convergent structure.

Key: The channel must be LINEAR (rank-monotone) so that:
  rank(channel(p)) ≤ rank(p)
This means high rank in output → high rank in input.
We want: channel(product) → high rank, channel(sum) → low rank,
         channel(TM-coupled) → high rank (coupling now VISIBLE)
"""

import numpy as np
from itertools import combinations, product as cart_product
from collections import defaultdict
from sympy import symbols, expand, Poly, ZZ, Rational
from sympy import prod as sym_prod
from functools import reduce

# ─── Polynomial infrastructure ───

def make_vars(n_content, n_state):
    """Create content variables x_0..x_{n-1} and state variables s_0..s_{m-1}"""
    xs = symbols(f'x0:{n_content}')
    ss = symbols(f's0:{n_state}')
    return list(xs), list(ss)

def get_monomials(poly, variables):
    """Extract {monomial_tuple: coeff} from expanded polynomial"""
    p = Poly(expand(poly), *variables, domain='ZZ')
    result = {}
    for monom, coeff in p.as_dict().items():
        if coeff != 0:
            result[monom] = int(coeff)
    return result

# ─── Markov Channel: Partial Trace ───

def partial_trace_channel(poly, content_vars, state_vars):
    """
    Markov channel: "trace out" state variables by setting them to all 
    combinations of {0, 1} and summing the resulting content-only polynomials.
    
    This is the polynomial analogue of quantum partial trace:
      Tr_S(ρ) = Σ_{s∈{0,1}^m} <s|ρ|s>
    
    For polynomials: channel(p)(x) = Σ_{s∈{0,1}^m} p(x, s)
    
    This is LINEAR in p, so rank-monotone.
    The sum over s "collapses" state variables but PRESERVES their 
    mediation effect as cross-terms in content variables.
    """
    result = 0
    n_state = len(state_vars)
    for bits in cart_product([0, 1], repeat=n_state):
        subs = {state_vars[i]: bits[i] for i in range(n_state)}
        result += poly.subs(subs)
    return expand(result)

def partial_trace_weighted(poly, content_vars, state_vars):
    """
    Weighted partial trace: instead of uniform sum, weight by 
    s_i * (1-s_i) to emphasize states that MEDIATE coupling.
    
    channel(p)(x) = Σ_{s} w(s) * p(x, s)
    where w(s) = Π_i s_i(1-s_i) ... no, this kills everything on {0,1}.
    
    Better: use derivative-based trace.
    channel(p)(x) = Σ_i ∂p/∂s_i |_{s=0}
    
    This extracts the LINEAR coupling through each state variable.
    Also linear in p, so rank-monotone.
    """
    from sympy import diff
    result = 0
    for sv in state_vars:
        dp = diff(poly, sv)
        subs = {s: 0 for s in state_vars}
        result += dp.subs(subs)
    return expand(result)

def derivative_trace_order_k(poly, content_vars, state_vars, k=1):
    """
    Order-k derivative trace: take k-th derivatives w.r.t. state vars,
    evaluate at s=0, sum over all k-subsets.
    
    channel_k(p)(x) = Σ_{|S|=k, S⊆state_vars} (∂^k p / ∂s_S)|_{s=0}
    
    k=0: just evaluate at s=0 (ignores state vars entirely)
    k=1: linear coupling through state vars
    k=2: pairwise state-variable coupling effects
    """
    from sympy import diff
    result = 0
    for subset in combinations(state_vars, k):
        dp = poly
        for sv in subset:
            dp = diff(dp, sv)
        subs = {s: 0 for s in state_vars}
        result += dp.subs(subs)
    return expand(result)

# ─── Möbius analysis on channel output ───

def coeff_mass(poly, variables, var_subset_indices):
    """Sum of |coeff| for monomials touching only vars in subset"""
    if poly == 0:
        return 0
    subset_vars = [variables[i] for i in var_subset_indices]
    other_vars = [v for i,v in enumerate(variables) if i not in var_subset_indices]
    # Set other vars to 0
    subs = {v: 0 for v in other_vars}
    restricted = expand(poly.subs(subs))
    if restricted == 0:
        return 0
    # Sum absolute coefficients
    try:
        p = Poly(restricted, *subset_vars, domain='ZZ')
        return sum(abs(c) for c in p.as_dict().values())
    except:
        return abs(int(restricted)) if restricted != 0 else 0

def mobius_inversion(f_values, n):
    """
    Given f_values[S] for S ⊆ {0..n-1}, compute Möbius inversion:
    f̂_T = Σ_{S⊆T} (-1)^{|T\S|} f_S
    
    Returns dict of f̂_T values keyed by frozenset T.
    """
    result = {}
    for size in range(n+1):
        for T in combinations(range(n), size):
            T_set = frozenset(T)
            val = 0
            # Sum over all subsets S of T
            T_list = list(T)
            for k in range(len(T_list)+1):
                for S in combinations(T_list, k):
                    S_set = frozenset(S)
                    sign = (-1) ** (len(T_set) - len(S_set))
                    val += sign * f_values.get(S_set, 0)
            result[T_set] = val
    return result

def analyze_mobius(poly, content_vars, n_clauses, clause_size=2):
    """
    Full Möbius analysis: compute f_S for each clause subset,
    then Möbius-invert to get f̂_T.
    
    Clause i uses content_vars[i*clause_size : (i+1)*clause_size]
    """
    # Compute f_S for all subsets of clauses
    f_values = {}
    for size in range(n_clauses + 1):
        for S in combinations(range(n_clauses), size):
            S_set = frozenset(S)
            var_indices = []
            for i in S:
                var_indices.extend(range(i*clause_size, (i+1)*clause_size))
            f_values[S_set] = coeff_mass(poly, content_vars, var_indices)
    
    # Möbius inversion
    fhat = mobius_inversion(f_values, n_clauses)
    return f_values, fhat

# ─── Test models ───

def build_models(n_clauses=3, clause_size=2):
    """
    Build test polynomials with n_clauses, each clause is AND of clause_size vars.
    State variables model TM computation coupling.
    """
    n_content = n_clauses * clause_size
    n_state = n_clauses  # one state var per time step
    
    content_vars, state_vars = make_vars(n_content, n_state)
    all_vars = content_vars + state_vars
    
    # Clause gadgets: G_i = x_{2i} * x_{2i+1}
    gates = []
    for i in range(n_clauses):
        g = content_vars[i*clause_size]
        for j in range(1, clause_size):
            g = g * content_vars[i*clause_size + j]
        gates.append(g)
    
    models = {}
    
    # 1. Pure product: Π(1 - G_i)
    models['pure_product'] = reduce(lambda a,b: expand(a*b), [1 - g for g in gates])
    
    # 2. Pure sum: Σ G_i
    models['pure_sum'] = sum(gates)
    
    # 3. Sum of squares: Σ G_i²
    models['sum_squares'] = sum(g**2 for g in gates)
    
    # 4. TM coupled: s_0 = G_0, s_t = s_{t-1} * (1 - G_t) + G_t
    #    (state carries forward, each step depends on previous state + current gate)
    tm_poly = state_vars[0] - gates[0]  # constraint: s_0 = G_0
    for t in range(1, n_clauses):
        # s_t = s_{t-1}*(1-G_t) + G_t  →  constraint: s_t - s_{t-1}*(1-G_t) - G_t = 0
        constraint = state_vars[t] - state_vars[t-1]*(1 - gates[t]) - gates[t]
        tm_poly = expand(tm_poly * constraint)
    models['tm_coupled'] = expand(tm_poly)
    
    # 5. TM violation (sum of squared constraints)
    c0 = state_vars[0] - gates[0]
    violations = [c0**2]
    for t in range(1, n_clauses):
        ct = state_vars[t] - state_vars[t-1]*(1 - gates[t]) - gates[t]
        violations.append(expand(ct**2))
    models['tm_violation'] = expand(sum(violations))
    
    # 6. TM product (product of (1-constraint²))
    models['tm_product'] = reduce(lambda a,b: expand(a*b), 
                                   [1 - v for v in violations])
    
    return models, content_vars, state_vars, gates, n_clauses

# ─── Main experiment ───

def run_experiment():
    n_clauses = 3
    clause_size = 2
    
    models, content_vars, state_vars, gates, nc = build_models(n_clauses, clause_size)
    all_vars = content_vars + state_vars
    
    print(f"=== Universal Markov Channel Bridge ===")
    print(f"Clauses: {nc}, Content vars: {len(content_vars)}, State vars: {len(state_vars)}")
    print()
    
    # For "raw", only analyze models without state vars
    channels = {
        'raw (content-only models)': lambda p: expand(p.subs({s: 0 for s in state_vars})),
        'partial_trace (Σ over s∈{0,1}^m)': lambda p: partial_trace_channel(p, content_vars, state_vars),
        'deriv_trace_k1 (Σ ∂p/∂s_i|_{s=0})': lambda p: partial_trace_weighted(p, content_vars, state_vars),
        'deriv_trace_k2 (Σ ∂²p/∂s_i∂s_j|_{s=0})': lambda p: derivative_trace_order_k(p, content_vars, state_vars, k=2),
    }
    
    for channel_name, channel_fn in channels.items():
        print(f"\n{'='*60}")
        print(f"CHANNEL: {channel_name}")
        print(f"{'='*60}")
        
        for model_name, poly in models.items():
            print(f"\n  --- {model_name} ---")
            
            # Apply channel
            try:
                output = channel_fn(poly)
            except Exception as e:
                print(f"    ERROR: {e}")
                continue
            
            if output == 0:
                print(f"    Output: 0 (trivial)")
                continue
            
            # Möbius analysis on channel output (content vars only)
            f_vals, fhat = analyze_mobius(output, content_vars, nc, clause_size)
            
            # Print f̂_T by level
            for level in range(nc + 1):
                vals = []
                for T in combinations(range(nc), level):
                    T_set = frozenset(T)
                    v = fhat[T_set]
                    if v != 0:
                        vals.append((T, v))
                if vals:
                    print(f"    |T|={level}: {vals}")
                else:
                    print(f"    |T|={level}: all zero")
            
            # Summary: total Möbius mass per level
            print(f"    Möbius mass by level: ", end="")
            for level in range(nc + 1):
                total = sum(abs(fhat[frozenset(T)]) for T in combinations(range(nc), level))
                print(f"|T|={level}→{total}  ", end="")
            print()

    # === NEW: Coarse-grained channel ===
    # Key insight from quantum paper: partial trace over FINE variables,
    # keeping COARSE structure. Here: the "fine" variables are individual
    # state vars; "coarse" is their cumulative effect.
    
    print(f"\n\n{'='*60}")
    print(f"COARSE-GRAINED CHANNELS (quantum paper inspired)")
    print(f"{'='*60}")
    
    # Channel: evaluate state vars along the COMPUTATION PATH
    # i.e., substitute s_t = f(s_{t-1}, G_t) recursively, eliminating state vars
    # This "compiles out" the TM, leaving only content-variable polynomial
    print(f"\n--- Recursive state elimination ---")
    for model_name in ['tm_coupled', 'tm_violation', 'tm_product']:
        poly = models[model_name]
        # Recursively substitute: s_0 = G_0, s_t = s_{t-1}*(1-G_t) + G_t
        elim_poly = poly
        # Forward substitution
        state_expr = gates[0]  # s_0 = G_0
        elim_poly = expand(elim_poly.subs(state_vars[0], state_expr))
        for t in range(1, nc):
            state_expr = expand(state_expr * (1 - gates[t]) + gates[t])
            elim_poly = expand(elim_poly.subs(state_vars[t], state_expr))
        
        print(f"\n  {model_name} after state elimination:")
        if elim_poly == 0:
            print(f"    Output: 0 (constraints satisfied → trivial)")
        else:
            f_vals, fhat = analyze_mobius(elim_poly, content_vars, nc, clause_size)
            for level in range(nc + 1):
                vals = []
                for T in combinations(range(nc), level):
                    T_set = frozenset(T)
                    v = fhat[T_set]
                    if v != 0:
                        vals.append((T, v))
                if vals:
                    print(f"    |T|={level}: {vals}")
                else:
                    print(f"    |T|={level}: all zero")
            
            print(f"    Möbius mass by level: ", end="")
            for level in range(nc + 1):
                total = sum(abs(fhat[frozenset(T)]) for T in combinations(range(nc), level))
                print(f"|T|={level}→{total}  ", end="")
            print()

if __name__ == '__main__':
    run_experiment()
