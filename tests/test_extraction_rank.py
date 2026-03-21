#!/usr/bin/env python3
"""
Falsification test for extraction_rank_monotone.

The axiom says: for any DTM M, n ≥ 2,
  blockedSpdpRankQ(log₂(√n*√n), log₂(√n*√n), permPolyFlat(√n), extractionBP(k,n))
  ≤ blockedSpdpRankQ(log₂(n), log₂(n), compiledPolyQ(cnf), tableauPartition)

We test this computationally for small n by:
1. Computing the permanent polynomial on m×m variables (m = floor(√n))
2. Computing a toy "compiled polynomial" (product of clauses from a simple CNF)
3. Computing blocked SPDP ranks under various block partitions
4. Checking the inequality

Key insight for falsification: the permanent polynomial has high SPDP rank
(grows super-polynomially). The compiled polynomial's rank depends on the
encoding. If the encoding is "wrong" or the block partition doesn't align,
the inequality could fail.
"""

import numpy as np
from itertools import product, combinations
from collections import defaultdict
import math

def isqrt(n):
    return int(math.isqrt(n))

def nat_log2(n):
    """Floor of log base 2, matching Lean's Nat.log 2"""
    if n <= 0: return 0
    return n.bit_length() - 1

# === Multivariate polynomial representation ===
# Polynomials as dict: {monomial_tuple: coefficient}
# monomial_tuple = tuple of (var_index, power) pairs, sorted

def poly_zero():
    return {}

def poly_const(c):
    if c == 0: return {}
    return {(): c}

def poly_var(i):
    """Variable x_i"""
    return {((i, 1),): 1}

def poly_add(p, q):
    result = dict(p)
    for m, c in q.items():
        result[m] = result.get(m, 0) + c
        if result[m] == 0:
            del result[m]
    return result

def poly_sub(p, q):
    return poly_add(p, {m: -c for m, c in q.items()})

def poly_mul(p, q):
    result = {}
    for mp, cp in p.items():
        for mq, cq in q.items():
            # Merge monomials
            merged = {}
            for v, e in mp:
                merged[v] = merged.get(v, 0) + e
            for v, e in mq:
                merged[v] = merged.get(v, 0) + e
            m = tuple(sorted(merged.items()))
            result[m] = result.get(m, 0) + cp * cq
            if result[m] == 0:
                del result[m]
    return result

def poly_total_degree(p):
    if not p: return 0
    return max(sum(e for _, e in m) for m in p.keys())

def poly_vars(p):
    """Set of variable indices appearing in p"""
    vs = set()
    for m in p.keys():
        for v, _ in m:
            vs.add(v)
    return vs

# === Permanent polynomial ===
def perm_poly(m):
    """Permanent of m×m matrix of variables x_{i*m+j}"""
    from itertools import permutations
    if m == 0:
        return poly_const(1)
    result = poly_zero()
    for perm in permutations(range(m)):
        term = poly_const(1)
        for i in range(m):
            j = perm[i]
            var_idx = i * m + j
            term = poly_mul(term, poly_var(var_idx))
        result = poly_add(result, term)
    return result

# === Partial derivative ===
def poly_pderiv(p, var_idx):
    """Partial derivative with respect to variable var_idx"""
    result = {}
    for m, c in p.items():
        # Find var_idx in monomial
        new_m = []
        coeff_mult = 0
        for v, e in m:
            if v == var_idx:
                coeff_mult = e
                if e > 1:
                    new_m.append((v, e - 1))
            else:
                new_m.append((v, e))
        if coeff_mult > 0:
            new_m_tuple = tuple(new_m)
            result[new_m_tuple] = result.get(new_m_tuple, 0) + c * coeff_mult
            if result[new_m_tuple] == 0:
                del result[new_m_tuple]
    return result

def iter_deriv_list(p, var_list):
    """Apply partial derivatives for each variable in var_list"""
    for v in var_list:
        p = poly_pderiv(p, v)
    return p

# === Blocked SPDP rank ===
def blocked_spdp_rank(kappa, ell, poly, block_of, num_vars):
    """
    Compute blocked SPDP rank.
    Generators: m * ∂^S(poly) where:
    - S is a list of derivative vars, |S| ≤ kappa, block-admissible (≤ kappa blocks)
    - m is a shift monomial, totalDegree ≤ ell, block-admissible (≤ ell blocks)
    
    Returns the dimension of the span of these generators.
    """
    generators = []
    var_indices = list(range(num_vars))
    
    # Generate all valid (S, m) pairs
    # S: subsets of variables of size ≤ kappa, with ≤ kappa distinct blocks
    for s_size in range(kappa + 1):
        for S in combinations(var_indices, s_size):
            # Check block admissibility of S
            s_blocks = set(block_of[v] for v in S)
            if len(s_blocks) > kappa:
                continue
            
            deriv = iter_deriv_list(poly, S)
            if not deriv:
                continue
            
            # Shift monomials: products of variables with total degree ≤ ell
            # and ≤ ell distinct blocks
            # For simplicity, enumerate monomials up to degree ell
            for m_deg in range(ell + 1):
                for m_vars in combinations_with_replacement(var_indices, m_deg):
                    m_blocks = set(block_of[v] for v in m_vars)
                    if len(m_blocks) > ell:
                        continue
                    # Build monomial
                    mono = poly_const(1)
                    for v in m_vars:
                        mono = poly_mul(mono, poly_var(v))
                    
                    gen = poly_mul(mono, deriv)
                    if gen:
                        generators.append(gen)
    
    if not generators:
        return 0
    
    # Convert generators to vectors and compute rank
    # Collect all monomials
    all_monos = set()
    for g in generators:
        all_monos.update(g.keys())
    all_monos = sorted(all_monos)
    mono_to_idx = {m: i for i, m in enumerate(all_monos)}
    
    # Build matrix
    matrix = np.zeros((len(generators), len(all_monos)))
    for i, g in enumerate(generators):
        for m, c in g.items():
            matrix[i, mono_to_idx[m]] = c
    
    # Rank = dimension of row space
    rank = np.linalg.matrix_rank(matrix)
    return rank

def combinations_with_replacement(iterable, r):
    """Like itertools.combinations_with_replacement"""
    from itertools import combinations_with_replacement as cwr
    return cwr(iterable, r)

# === Block partitions ===
def identity_partition(N):
    return list(range(N))

def one_block_partition(N):
    return [0] * N

def tableau_partition(N, chunk=2):
    """Time-slice partition: (v // chunk) % 3"""
    return [(v // chunk) % 3 for v in range(N)]

def pullback_partition(target_bp, embedding):
    """Pullback of target_bp through embedding function"""
    return [target_bp[embedding(v)] for v in range(len(target_bp))]

# === Compiled polynomial (simple CNF) ===
def simple_cnf_poly(num_vars, clauses):
    """
    Compiled polynomial = product of clause polynomials.
    Each clause is a list of (var, positive) literals.
    clausePoly(c) = 1 - product(1 - litPoly(l) for l in c)
    litPoly(v, True) = x_v, litPoly(v, False) = 1 - x_v
    """
    result = poly_const(1)
    for clause in clauses:
        clause_poly = poly_const(1)
        for var, positive in clause:
            if positive:
                lit = poly_var(var)
            else:
                lit = poly_sub(poly_const(1), poly_var(var))
            clause_poly = poly_mul(clause_poly, poly_sub(poly_const(1), lit))
        clause_poly = poly_sub(poly_const(1), clause_poly)
        result = poly_mul(result, clause_poly)
    return result

# === Test extraction_rank_monotone ===
def test_extraction_rank(n):
    """
    Test extraction_rank_monotone for a given n.
    
    LHS: blockedSpdpRankQ(log₂(m*m), log₂(m*m), permPolyFlat(m), extractionBP)
    RHS: blockedSpdpRankQ(log₂(n), log₂(n), compiledPolyQ(cnf), tableauPartition)
    
    where m = isqrt(n)
    """
    m = isqrt(n)
    if m < 2:
        print(f"n={n}: m={m} < 2, skip")
        return True
    
    num_perm_vars = m * m
    kappa_lhs = nat_log2(num_perm_vars)
    ell_lhs = kappa_lhs
    kappa_rhs = nat_log2(n)
    ell_rhs = kappa_rhs
    
    print(f"\nn={n}, m={m}, perm_vars={num_perm_vars}")
    print(f"  LHS params: κ=ℓ={kappa_lhs}")
    print(f"  RHS params: κ=ℓ={kappa_rhs}")
    
    # Permanent polynomial
    perm = perm_poly(m)
    print(f"  perm_poly: {len(perm)} terms, degree {poly_total_degree(perm)}")
    
    # For the RHS: we need a compiled polynomial on compiledVarCount variables.
    # compiledVarCount(k, n) = n^(2k+1) for some k (machine time bound).
    # For testing, use k=1 so compiledVarCount = n^3
    k = 1
    compiled_var_count = n ** (2 * k + 1)
    
    print(f"  compiled_var_count (k={k}): {compiled_var_count}")
    
    if compiled_var_count > 50:
        print(f"  Too many compiled vars, using reduced test")
        # Use a simpler test: just compute LHS rank
        # The extraction BP is a pullback of the tableau partition on compiled vars
        # through the embedding (identity on first m*m vars)
        
        # For the extraction BP, each perm var i maps to compiled var i
        # Then bp[i] = tableauPartition(compiled_var_count)[i]
        extraction_bp = [tableau_partition(compiled_var_count, chunk=2)[i] for i in range(num_perm_vars)]
        
        print(f"  extraction_bp: {extraction_bp[:10]}...")
        
        lhs_rank = blocked_spdp_rank(kappa_lhs, ell_lhs, perm, extraction_bp, num_perm_vars)
        print(f"  LHS rank (perm under extraction BP): {lhs_rank}")
        
        # For RHS, we can't compute with n^3 vars.
        # But we know the compiled polynomial is a product of clause polynomials.
        # A trivial CNF (no clauses) gives compiledPoly = 1, rank = 0.
        # A CNF encoding the permanent would give compiled rank ≥ perm rank.
        # The question is: does the Cook-Levin CNF for a specific DTM actually
        # encode the permanent correctly?
        
        print(f"  (RHS not computed — compiled var count too large)")
        print(f"  LHS rank = {lhs_rank}. For axiom to hold, RHS ≥ {lhs_rank}")
        return None  # Can't verify
    
    # Small enough to compute both sides
    # Build a toy CNF on compiled_var_count vars
    # For falsification: use a RANDOM CNF and check if the inequality can fail
    import random
    random.seed(42 + n)
    
    num_clauses = max(3, compiled_var_count // 2)
    clauses = []
    for _ in range(num_clauses):
        clause_size = min(3, compiled_var_count)
        clause_vars = random.sample(range(compiled_var_count), clause_size)
        clause = [(v, random.choice([True, False])) for v in clause_vars]
        clauses.append(clause)
    
    compiled = simple_cnf_poly(compiled_var_count, clauses)
    print(f"  compiled_poly: {len(compiled)} terms, degree {poly_total_degree(compiled)}")
    
    tableau_bp = tableau_partition(compiled_var_count)
    
    # Embedding: perm var i → compiled var i  
    embedding = lambda v: v
    extraction_bp = [tableau_bp[embedding(v)] for v in range(num_perm_vars)]
    
    lhs_rank = blocked_spdp_rank(kappa_lhs, ell_lhs, perm, extraction_bp, num_perm_vars)
    rhs_rank = blocked_spdp_rank(kappa_rhs, ell_rhs, compiled, tableau_bp, compiled_var_count)
    
    print(f"  LHS rank (perm): {lhs_rank}")
    print(f"  RHS rank (compiled): {rhs_rank}")
    
    if lhs_rank > rhs_rank:
        print(f"  *** COUNTEREXAMPLE: LHS={lhs_rank} > RHS={rhs_rank} ***")
        return False
    else:
        print(f"  OK: LHS ≤ RHS")
        return True

# Run tests
print("=" * 60)
print("Testing extraction_rank_monotone for small n")
print("=" * 60)

for n in [4, 5, 6, 7, 8, 9]:
    result = test_extraction_rank(n)
    if result is False:
        print(f"\n*** FALSIFIED at n={n} ***")
        break
