#!/usr/bin/env python3
"""
Structured channel: use the computational graph to define a rank measure
that DOES distinguish verifier from solver.

Key insight from experiments:
- SPDP rank alone sees both as "product of local terms" → same rank
- Need to incorporate GRAPH STRUCTURE of the computation

Idea: The verifier's constraint graph is an EXPANDER (high girth).
The solver's constraint graph is a CHAIN (sequential TM steps).
These have different spectral properties.

Define: spectral SPDP rank = SPDP rank weighted by graph Laplacian eigenvalues.

Or simpler: SPDP rank restricted to derivatives along INDEPENDENT SETS
of the constraint graph. Expanders have large independent sets;
chains have smaller ones (relatively).

Wait — actually chains have independent sets of size n/2 too.
The difference must be more subtle.

NEW IDEA: The difference is in the PARTITION, not the polynomial.
The SPDP rank depends on the block partition B.
- NP side: B = tseitinPartition (one block per clause, disjoint)
- P side: B = compilerPartition (one block per gate)

What if the P-side partition has FEWER blocks that are WIDER?
Then the blocked rank is smaller.

Actually... this IS what profile decomposition does.
The P-side collapse already works in the existing proof.
The issue is connecting the two sides.

Let me try something different: CONDITIONAL rank.
"""
import numpy as np
from itertools import combinations
from collections import defaultdict

def poly_mul(p1, p2):
    result = defaultdict(int)
    for m1, c1 in p1.items():
        for m2, c2 in p2.items():
            if m1 & m2: continue
            result[m1 | m2] += c1 * c2
    return {m: c for m, c in result.items() if c != 0}

def poly_add(p1, p2):
    result = defaultdict(int)
    for m, c in p1.items(): result[m] += c
    for m, c in p2.items(): result[m] += c
    return {m: c for m, c in result.items() if c != 0}

def poly_neg(p): return {m: -c for m, c in p.items()}
def X(i): return {frozenset([i]): 1}
def C(c): return {frozenset(): c} if c else {}

def pderiv(p, v):
    result = defaultdict(int)
    for m, c in p.items():
        if v in m: result[m - {v}] += c
    return {m: c for m, c in result.items() if c != 0}

def spdp_rank(poly, variables, kappa):
    derivs = []
    for combo in combinations(variables, kappa):
        d = poly
        for v in combo:
            d = pderiv(d, v)
            if not d: break
        if d: derivs.append(d)
    if not derivs: return 0
    all_m = sorted(set().union(*(d.keys() for d in derivs)), key=lambda s: (len(s), tuple(sorted(s))))
    mi = {m: i for i, m in enumerate(all_m)}
    mat = np.zeros((len(derivs), len(all_m)))
    for i, d in enumerate(derivs):
        for m, c in d.items(): mat[i, mi[m]] = c
    return int(np.linalg.matrix_rank(mat))

def blocked_spdp_rank(poly, partition, kappa):
    """
    Blocked SPDP rank: only take derivatives using variables from
    kappa DIFFERENT blocks (one variable per block).
    
    This is the actual SPDP measure in the paper.
    partition = list of lists of variables (blocks)
    """
    n_blocks = len(partition)
    if kappa > n_blocks:
        return 0
    
    derivs = []
    for block_combo in combinations(range(n_blocks), kappa):
        # For each combination of kappa blocks, try all ways to pick one var per block
        block_vars = [partition[b] for b in block_combo]
        for var_choice in _cartesian(block_vars):
            d = poly
            for v in var_choice:
                d = pderiv(d, v)
                if not d: break
            if d:
                derivs.append(d)
    
    if not derivs: return 0
    all_m = sorted(set().union(*(d.keys() for d in derivs)), key=lambda s: (len(s), tuple(sorted(s))))
    mi = {m: i for i, m in enumerate(all_m)}
    mat = np.zeros((len(derivs), len(all_m)))
    for i, d in enumerate(derivs):
        for m, c in d.items(): mat[i, mi[m]] = c
    return int(np.linalg.matrix_rank(mat))

def _cartesian(lists):
    if not lists: yield (); return
    for x in lists[0]:
        for rest in _cartesian(lists[1:]):
            yield (x,) + rest

# === Build polynomials ===
def build_verifier(n):
    """NP verifier: ∏(1 - z_i · G_i), partition = one block per clause"""
    p = C(1)
    partition = []
    for i in range(n):
        z_i = X(1000 + i)
        G_i = poly_add(X(2*i), X(2*i+1))
        p = poly_mul(p, poly_add(C(1), poly_neg(poly_mul(z_i, G_i))))
        partition.append([1000+i, 2*i, 2*i+1])  # clause block
    return p, partition

def build_solver_fresh(n):
    """TM solver with fresh vars: ∏(1 - q_t · G_t), partition = one block per step"""
    p = C(1)
    partition = []
    for t in range(n):
        q_t = X(2000 + t)
        G_t = poly_add(X(2*t), X(2*t+1))
        p = poly_mul(p, poly_add(C(1), poly_neg(poly_mul(q_t, G_t))))
        partition.append([2000+t, 2*t, 2*t+1])
    return p, partition

def build_solver_wide_blocks(n, block_width):
    """
    TM solver with WIDE blocks: group multiple time steps per block.
    This models a TM that processes multiple clauses per "stage".
    
    If block_width = n, single block → rank = O(1).
    If block_width = 1, one block per step → rank = superpoly.
    """
    p = C(1)
    partition = []
    current_block = []
    for t in range(n):
        q_t = X(2000 + t)
        G_t = poly_add(X(2*t), X(2*t+1))
        p = poly_mul(p, poly_add(C(1), poly_neg(poly_mul(q_t, G_t))))
        current_block.extend([2000+t, 2*t, 2*t+1])
        if len(current_block) >= block_width * 3 or t == n-1:
            partition.append(current_block)
            current_block = []
    return p, partition

print("=" * 70)
print("BLOCKED SPDP RANK — partition matters!")
print("=" * 70)

print("\n--- Same polynomial, different partitions ---")
print("Verifier and solver(fresh) are algebraically isomorphic.")
print("But they could have different NATURAL partitions.")
print()
print(f"{'n':>4} {'verif(nat)':>11} {'solver(nat)':>12} {'solver(wide2)':>14} {'solver(wideN)':>14}  κ=2")
for n in range(2, 7):
    v_p, v_part = build_verifier(n)
    s_p, s_part = build_solver_fresh(n)
    _, sw2_part = build_solver_wide_blocks(n, 2)
    _, swn_part = build_solver_wide_blocks(n, n)
    
    vr = blocked_spdp_rank(v_p, v_part, 2)
    sr = blocked_spdp_rank(s_p, s_part, 2)
    # Use solver polynomial with wide partitions
    sw2r = blocked_spdp_rank(s_p, sw2_part, 2)
    swnr = blocked_spdp_rank(s_p, swn_part, 2)
    
    print(f"{n:>4} {vr:>11} {sr:>12} {sw2r:>14} {swnr:>14}")

print()
print("--- Key test: SAME polynomial, verifier partition vs wide partition ---")
print("This tests whether PARTITION CHOICE alone can create the separation.")
print(f"{'n':>4} {'1-block-per':>12} {'2-per-block':>12} {'all-in-one':>12}  κ=2")
for n in range(2, 7):
    p, _ = build_verifier(n)  # same polynomial
    
    # Partition 1: one clause per block (fine)
    part_fine = [[1000+i, 2*i, 2*i+1] for i in range(n)]
    # Partition 2: two clauses per block
    part_med = []
    for i in range(0, n, 2):
        block = [1000+i, 2*i, 2*i+1]
        if i+1 < n:
            block += [1000+i+1, 2*(i+1), 2*(i+1)+1]
        part_med.append(block)
    # Partition 3: all in one block
    part_one = [sum([[1000+i, 2*i, 2*i+1] for i in range(n)], [])]
    
    r_fine = blocked_spdp_rank(p, part_fine, 2)
    r_med = blocked_spdp_rank(p, part_med, 2)
    r_one = blocked_spdp_rank(p, part_one, 2)
    
    print(f"{n:>4} {r_fine:>12} {r_med:>12} {r_one:>12}")

print()
print("=" * 70)
print("""
INSIGHT: The blocked SPDP rank depends on the PARTITION.
Same polynomial can have superpoly rank (fine partition)
or poly rank (coarse partition).

The P-side NATURAL partition is determined by the compiler structure.
A poly-time TM compiled with T=poly(n) gates has T blocks.
If each block is O(1) width, there are Ω(n) blocks → superpoly blocked rank.

To get poly blocked rank, you need O(log n) or fewer blocks.
But a TM with poly(n) steps can't be described with O(log n) blocks.

UNLESS: the Markov bridge RE-PARTITIONS.
The bridge maps the fine TM partition to a coarser partition
while preserving the polynomial identity.

This is the "partial trace" / "coarse-graining" idea:
the bridge is a PARTITION REFINEMENT MAP.
""")

# Final test: can re-partitioning create a valid bridge?
print("--- Final: Re-partition bridge ---")
print("NP side: fine partition (n blocks) → superpoly rank")
print("Map to: coarse partition (√n blocks) → what rank?")
print(f"{'n':>4} {'fine(n blk)':>12} {'√n blk':>8} {'2 blk':>8} {'1 blk':>8}  κ=2")
for n in [4, 6, 8, 9]:
    p, _ = build_verifier(n)
    all_clause_vars = sum([[1000+i, 2*i, 2*i+1] for i in range(n)], [])
    
    # Fine: n blocks
    part_n = [[1000+i, 2*i, 2*i+1] for i in range(n)]
    
    # √n blocks
    sqn = max(2, int(n**0.5))
    part_sq = []
    for b in range(sqn):
        start = b * n // sqn
        end = (b+1) * n // sqn
        block = sum([[1000+i, 2*i, 2*i+1] for i in range(start, end)], [])
        if block: part_sq.append(block)
    
    # 2 blocks
    half = n // 2
    part_2 = [
        sum([[1000+i, 2*i, 2*i+1] for i in range(half)], []),
        sum([[1000+i, 2*i, 2*i+1] for i in range(half, n)], [])
    ]
    
    # 1 block
    part_1 = [all_clause_vars]
    
    r_n = blocked_spdp_rank(p, part_n, 2)
    r_sq = blocked_spdp_rank(p, part_sq, 2)
    r_2 = blocked_spdp_rank(p, part_2, 2)
    r_1 = blocked_spdp_rank(p, part_1, 2)
    
    print(f"{n:>4} {r_n:>12} {r_sq:>8} {r_2:>8} {r_1:>8}")

print("\n" + "=" * 70)
