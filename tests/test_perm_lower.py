#!/usr/bin/env python3
"""
Test permanent_spdp_lower (Theorem 94):
  ∃ m₀, ∀ m ≥ m₀, ∀ bp, blockedSpdpRank(log₂(m²), log₂(m²), perm(m), bp) > m

And check the extraction_rank_monotone LHS values to see if they're
consistent with the proof chain.
"""
import sys
sys.path.insert(0, '/tmp/pall-lean/tests')
from test_extraction_rank import *

print("=" * 60)
print("Permanent SPDP rank lower bounds (Theorem 94)")
print("=" * 60)

for m in [2, 3]:
    n = m * m
    kappa = nat_log2(n)
    ell = kappa
    
    print(f"\nm={m}, n_vars={n}, κ=ℓ={kappa}")
    
    perm = perm_poly(m)
    print(f"  perm terms: {len(perm)}, degree: {poly_total_degree(perm)}")
    
    # Test with various block partitions
    for bp_name, bp in [
        ("identity", identity_partition(n)),
        ("one-block", one_block_partition(n)),
        ("tableau", tableau_partition(n)),
    ]:
        rank = blocked_spdp_rank(kappa, ell, perm, bp, n)
        print(f"  bp={bp_name}: rank={rank}, m={m}, rank > m? {rank > m}")

print("\n" + "=" * 60)
print("Extraction partition ranks (LHS of extraction_rank_monotone)")
print("=" * 60)

for n in [4, 9, 16]:
    m = isqrt(n)
    kappa = nat_log2(m * m)
    ell = kappa
    
    # Use k=1 for compiled var count
    k = 1
    cvc = n ** (2 * k + 1)
    
    # Extraction BP: pullback of tableau on cvc through identity embedding
    extraction_bp = [tableau_partition(cvc)[i] for i in range(m * m)]
    
    perm = perm_poly(m)
    rank = blocked_spdp_rank(kappa, ell, perm, extraction_bp, m * m)
    
    sqrt_n = isqrt(n)
    print(f"\nn={n}, m={m}, κ=ℓ={kappa}")
    print(f"  extraction BP: {extraction_bp}")
    print(f"  perm rank under extraction BP: {rank}")
    print(f"  √n = {sqrt_n}")
    print(f"  rank > √n? {rank > sqrt_n}")
    print(f"  (For P≠NP: need rank > √n AND rank ≤ compiled_rank ≤ √n → contradiction)")
