#!/usr/bin/env python3
"""Test blocked SPDP rank of the FULL compiled polynomial (no restriction).
This matches what the Lean axiom actually claims."""
import sys, numpy as np
from itertools import combinations
sys.path.insert(0, '/tmp/pall-lean/tests')
from test_extraction_rank import (
    poly_zero, poly_const, poly_var, poly_add, poly_sub, poly_mul,
    poly_total_degree, poly_vars, poly_pderiv, iter_deriv_list,
    nat_log2, combinations_with_replacement
)
from test_clause_survival import (
    make_cook_levin_cnf, clause_to_poly, compiled_poly_from_clauses,
    blocked_spdp_rank_small
)

print("=" * 70)
print("FULL COMPILED POLYNOMIAL — NO RESTRICTION")
print("=" * 70)

for tape_size in [2, 3]:
    for time_bound in [4]:
        n = time_bound * tape_size
        N = n  # total variables in the encoding
        kappa = nat_log2(N)
        ell = kappa
        
        clauses, N_check = make_cook_levin_cnf(time_bound, tape_size)
        assert N_check == N
        
        # Build FULL compiled polynomial — ALL clauses, ALL variables
        compiled = compiled_poly_from_clauses(clauses, N)
        
        print(f"\ntape={tape_size}, T={time_bound}, N={N}")
        print(f"  Total clauses: {len(clauses)}")
        print(f"  Compiled poly terms: {len(compiled)}, degree: {poly_total_degree(compiled)}")
        print(f"  κ=ℓ={kappa}")
        
        if N > 10:
            print(f"  Skipping rank (N={N} too large)")
            continue
        
        # Identity partition
        bp_id = list(range(N))
        rank_id = blocked_spdp_rank_small(kappa, ell, compiled, bp_id, N)
        print(f"  Identity partition ({N} blocks): rank = {rank_id}")
        
        # 3-block partition (tableauPartition style)
        bp_3 = [(v // 2) % 3 for v in range(N)]
        rank_3 = blocked_spdp_rank_small(kappa, ell, compiled, bp_3, N)
        print(f"  3-block partition: rank = {rank_3}")
        
        for c in range(1, 15):
            bound = (nat_log2(N) + 1) ** c
            if rank_3 <= bound:
                print(f"  3-block: fits (log₂{N}+1)^{c} = {bound}")
                break
        else:
            print(f"  3-block: DOES NOT FIT (log₂{N}+1)^c for c≤14! rank={rank_3}")
        
        for c in range(1, 15):
            bound = (nat_log2(N) + 1) ** c
            if rank_id <= bound:
                print(f"  Identity: fits (log₂{N}+1)^{c} = {bound}")
                break
        else:
            print(f"  Identity: DOES NOT FIT (log₂{N}+1)^c for c≤14! rank={rank_id}")
