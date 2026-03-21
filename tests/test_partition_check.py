#!/usr/bin/env python3
"""Check whether 3-block partition makes block-admissibility vacuous."""
import sys
sys.path.insert(0, '/tmp/pall-lean/tests')
from test_clause_survival import *

print("=" * 70)
print("PARTITION COMPARISON: identity vs 3-block")
print("=" * 70)

for tape_size in [2, 3]:
    for time_bound in [4, 8]:
        n = time_bound * tape_size
        num_live = max(1, nat_log2(n))
        kappa = num_live
        ell = num_live
        
        clauses, N = make_cook_levin_cnf(time_bound, tape_size)
        surviving, num_live_actual = apply_universal_restriction(clauses, N, num_live)
        
        if not surviving or num_live_actual > 8:
            continue
            
        compiled = compiled_poly_from_clauses(surviving, num_live_actual)
        
        print(f"\ntape={tape_size}, T={time_bound}, N={N}, live={num_live_actual}, κ=ℓ={kappa}")
        
        # Identity partition (each var = own block)
        bp_identity = list(range(num_live_actual))
        rank_id = blocked_spdp_rank_small(kappa, ell, compiled, bp_identity, num_live_actual)
        print(f"  Identity partition ({num_live_actual} blocks): rank = {rank_id}")
        
        # 3-block partition (tableauPartition style: (v/2) % 3)
        bp_3block = [(v // 2) % 3 for v in range(num_live_actual)]
        rank_3b = blocked_spdp_rank_small(kappa, ell, compiled, bp_3block, num_live_actual)
        print(f"  3-block partition: rank = {rank_3b}")
        
        # 1-block partition (everything in block 0 — should be same as unrestricted)
        bp_1block = [0] * num_live_actual
        rank_1b = blocked_spdp_rank_small(kappa, ell, compiled, bp_1block, num_live_actual)
        print(f"  1-block partition: rank = {rank_1b}")
        
        # Check: with 3-block partition and κ≥3, is block condition vacuous?
        print(f"  κ={kappa} ≥ 3? {kappa >= 3}")
        if kappa >= 3:
            print(f"  With 3 blocks and κ≥3: block condition IS vacuous")
            print(f"  So 3-block rank should equal 1-block rank: {rank_3b == rank_1b}")
        
        for c in range(1, 8):
            bound = (nat_log2(n) + 1) ** c
            if rank_3b <= bound:
                print(f"  3-block: fits (log₂{n}+1)^{c} = {bound}")
                break
        else:
            print(f"  3-block: DOES NOT FIT (log₂{n}+1)^c for c≤7! rank={rank_3b}")
