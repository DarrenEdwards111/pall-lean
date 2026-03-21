#!/usr/bin/env python3
"""
Empirical stress-test for restricted_clause_survival.

The axiom says: for any DTM M, ∃ c n₀, ∀ n ≥ n₀,
  blockedSpdpRankQ(log₂n, log₂n, compiledPolyQ(cnf), bp) ≤ (log₂n + 1)^c

We test this by:
1. Building a toy DTM (e.g., identity machine, constant machine)
2. Constructing a Cook-Levin-style width-3 CNF encoding
3. Applying universal restriction (fix all but log₂n variables)
4. Counting surviving (nontrivial) clauses
5. Computing blocked SPDP rank of the restricted polynomial
6. Checking if rank ≤ (log₂n + 1)^c for small c

The Cook-Levin encoding for a DTM with time bound T(n):
- N = O(T(n)²) variables (tape cell × time step)
- L = O(T(n)²) clauses: initial config, transitions, acceptance
- Each clause has width ≤ 3 (references ≤ 3 variables)
- Variables: v_{t,i} = "tape cell i at time t"

After universal restriction (fixing vars for t < T(n) - log₂n):
- Only vars for t ≥ T(n) - log₂n survive (log₂n time steps)
- Clauses entirely in fixed time steps become constants
- Only clauses straddling the boundary or in live region survive
"""

import numpy as np
from itertools import combinations
import math
import sys

sys.path.insert(0, '/tmp/pall-lean/tests')
from test_extraction_rank import (
    poly_zero, poly_const, poly_var, poly_add, poly_sub, poly_mul,
    poly_total_degree, poly_vars, poly_pderiv, iter_deriv_list,
    nat_log2, isqrt, combinations_with_replacement
)


def make_cook_levin_cnf(time_bound, tape_size):
    """
    Build a simplified Cook-Levin CNF.
    
    Variables: v_{t,i} for t=0..time_bound-1, i=0..tape_size-1
    Variable index: t * tape_size + i
    
    Clauses (simplified):
    1. Initial config: v_{0,i} = known (for each i)
       → unit clauses or pairs
    2. Transition: v_{t+1,i} depends on v_{t,i-1}, v_{t,i}, v_{t,i+1}
       → width-3 clauses linking consecutive time steps
    3. Consistency: at most one head position per time step
       → width-2 clauses
    
    Returns: list of clauses, each clause = list of (var_idx, positive)
    """
    N = time_bound * tape_size
    clauses = []
    
    def var_idx(t, i):
        return t * tape_size + i
    
    # Initial config clauses: v_{0,i} is fixed
    for i in range(tape_size):
        # v_{0,i} = False (initial tape is blank)
        clauses.append([(var_idx(0, i), False)])  # ¬v_{0,i}
    
    # Transition clauses: v_{t+1,i} depends on v_{t,i-1}, v_{t,i}, v_{t,i+1}
    for t in range(time_bound - 1):
        for i in range(tape_size):
            # Simplified: v_{t+1,i} ↔ majority(v_{t,max(0,i-1)}, v_{t,i}, v_{t,min(tape_size-1,i+1)})
            # This is a toy transition, not a real DTM
            left = max(0, i - 1)
            right = min(tape_size - 1, i + 1)
            
            # Forward implication (width 3): 
            # v_{t,left} ∧ v_{t,i} → v_{t+1,i}
            # As clause: ¬v_{t,left} ∨ ¬v_{t,i} ∨ v_{t+1,i}
            clauses.append([
                (var_idx(t, left), False),
                (var_idx(t, i), False),
                (var_idx(t + 1, i), True)
            ])
            
            # Backward implication (width 3):
            # v_{t+1,i} → v_{t,i} ∨ v_{t,right}
            # As clause: ¬v_{t+1,i} ∨ v_{t,i} ∨ v_{t,right}
            clauses.append([
                (var_idx(t + 1, i), False),
                (var_idx(t, i), True),
                (var_idx(t, right), True)
            ])
    
    return clauses, N


def apply_universal_restriction(clauses, N, num_live):
    """
    Universal restriction: fix variables 0..N-num_live-1 to False.
    Live variables: N-num_live..N-1.
    
    For each clause:
    - If any literal is satisfied by the restriction → clause is trivially true → drop
    - Remove falsified literals
    - If empty clause → contradiction (unsatisfiable after restriction)
    - Otherwise → surviving clause on live variables
    
    Returns: (surviving_clauses, live_var_map)
    where live_var_map[old_idx] = new_idx for live variables
    """
    fixed_cutoff = N - num_live  # vars < cutoff are fixed to False
    
    surviving = []
    for clause in clauses:
        satisfied = False
        remaining_lits = []
        for var, positive in clause:
            if var < fixed_cutoff:
                # Variable is fixed to False
                if not positive:
                    # ¬(False) = True → clause satisfied
                    satisfied = True
                    break
                # positive literal on False var → literal is False, drop it
            else:
                # Live variable
                remaining_lits.append((var - fixed_cutoff, positive))
        
        if satisfied:
            continue
        if remaining_lits:
            surviving.append(remaining_lits)
    
    return surviving, num_live


def clause_to_poly(clause, num_vars):
    """Convert a clause to polynomial: 1 - ∏(1 - lit)"""
    prod = poly_const(1)
    for var, positive in clause:
        if positive:
            lit = poly_var(var)
        else:
            lit = poly_sub(poly_const(1), poly_var(var))
        prod = poly_mul(prod, poly_sub(poly_const(1), lit))
    return poly_sub(poly_const(1), prod)


def compiled_poly_from_clauses(clauses, num_vars):
    """compiledPolyQ = ∏ clausePoly(c)"""
    result = poly_const(1)
    for clause in clauses:
        cp = clause_to_poly(clause, num_vars)
        result = poly_mul(result, cp)
    return result


def blocked_spdp_rank_small(kappa, ell, poly, block_of, num_vars):
    """Compute blocked SPDP rank for small instances."""
    generators = []
    var_indices = list(range(num_vars))
    
    for s_size in range(min(kappa + 1, num_vars + 1)):
        for S in combinations(var_indices, s_size):
            s_blocks = set(block_of[v] for v in S)
            if len(s_blocks) > kappa:
                continue
            
            deriv = iter_deriv_list(poly, S)
            if not deriv:
                continue
            
            for m_deg in range(ell + 1):
                for m_vars in combinations_with_replacement(var_indices, m_deg):
                    m_blocks = set(block_of[v] for v in m_vars)
                    if len(m_blocks) > ell:
                        continue
                    mono = poly_const(1)
                    for v in m_vars:
                        mono = poly_mul(mono, poly_var(v))
                    
                    gen = poly_mul(mono, deriv)
                    if gen:
                        generators.append(gen)
    
    if not generators:
        return 0
    
    all_monos = set()
    for g in generators:
        all_monos.update(g.keys())
    all_monos = sorted(all_monos)
    mono_to_idx = {m: i for i, m in enumerate(all_monos)}
    
    matrix = np.zeros((len(generators), len(all_monos)))
    for i, g in enumerate(generators):
        for m, c in g.items():
            matrix[i, mono_to_idx[m]] = c
    
    return int(np.linalg.matrix_rank(matrix))


# === Main tests ===

print("=" * 70)
print("RESTRICTED CLAUSE SURVIVAL STRESS TEST")
print("=" * 70)

for tape_size in [2, 3, 4]:
    for time_bound in [4, 6, 8, 10, 12]:
        n = time_bound * tape_size  # total variables
        num_live = max(1, nat_log2(n))
        kappa = num_live
        ell = num_live
        
        clauses, N = make_cook_levin_cnf(time_bound, tape_size)
        surviving, num_live_actual = apply_universal_restriction(clauses, N, num_live)
        
        print(f"\ntape={tape_size}, T={time_bound}, N={N}, live={num_live}")
        print(f"  Total clauses: {len(clauses)}")
        print(f"  Surviving clauses: {len(surviving)}")
        print(f"  κ=ℓ={kappa}")
        
        if num_live_actual > 8:
            print(f"  (too many live vars for SPDP computation, skip rank)")
            log_bound = (nat_log2(n) + 1)
            print(f"  (log₂{n}+1)^3 = {log_bound**3}")
            continue
        
        if not surviving:
            print(f"  No surviving clauses → compiled poly = 1, rank = 0")
            continue
            
        # Build compiled polynomial from surviving clauses
        compiled = compiled_poly_from_clauses(surviving, num_live_actual)
        print(f"  Compiled poly terms: {len(compiled)}, degree: {poly_total_degree(compiled)}")
        
        # Block partition: identity (each var = own block)
        bp = list(range(num_live_actual))
        
        try:
            rank = blocked_spdp_rank_small(kappa, ell, compiled, bp, num_live_actual)
            print(f"  Blocked SPDP rank: {rank}")
            
            for c in [1, 2, 3, 4, 5]:
                bound = (nat_log2(n) + 1) ** c
                status = "✓" if rank <= bound else "✗"
                print(f"    (log₂{n}+1)^{c} = {bound}: {status}")
                if rank <= bound:
                    print(f"    → restricted_clause_survival holds with c={c}")
                    break
        except Exception as e:
            print(f"  Rank computation failed: {e}")
