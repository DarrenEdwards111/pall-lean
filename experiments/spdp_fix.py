#!/usr/bin/env python3
"""
Fix: use proper boolean gadgets and non-multilinear arithmetic.
Also: test what happens when we evaluate on boolean hypercube.

Key insight to test: on boolean inputs (x∈{0,1}), 
product and sum encode the SAME boolean function.
Does this force any channel equivalence?
"""
import numpy as np
from itertools import combinations, product as cartprod
from collections import defaultdict

# NON-multilinear poly arithmetic (allow x^2 etc.)
# Monomial = tuple of (var, power) sorted by var
# Represent as dict: frozenset of (var, power) → coeff

def mono_mul(m1, m2):
    """Multiply two monomials (as dicts var→power)."""
    result = dict(m1)
    for v, p in m2.items():
        result[v] = result.get(v, 0) + p
    return frozenset(result.items())

def poly_mul_full(p1, p2):
    r = defaultdict(int)
    for m1, c1 in p1.items():
        for m2, c2 in p2.items():
            m = mono_mul(dict(m1), dict(m2))
            r[m] += c1 * c2
    return {m:c for m,c in r.items() if c}

def poly_add_full(p1, p2):
    r = defaultdict(int)
    for m,c in p1.items(): r[m]+=c
    for m,c in p2.items(): r[m]+=c
    return {m:c for m,c in r.items() if c}

def poly_neg_full(p): return {m:-c for m,c in p.items()}
def Xf(i): return {frozenset([(i,1)]): 1}
def Cf(c): return {frozenset(): c} if c else {}

def eval_full(p, assignment):
    """Evaluate polynomial at assignment."""
    result = 0
    for m, c in p.items():
        val = c
        for v, pw in m:
            if v in assignment:
                val *= assignment[v] ** pw
            else:
                return None
        result += val
    return result

# Build Tseitin-style clause: G_i = x_{2i} + x_{2i+1} - 1
# Satisfied when x_{2i}+x_{2i+1} = 1 (exactly one true)

def gadget(i):
    return poly_add_full(poly_add_full(Xf(2*i), Xf(2*i+1)), Cf(-1))

# Product: ∏(1-z_i·G_i)
def productPoly(n):
    p = Cf(1)
    for i in range(n):
        g = gadget(i)
        zg = poly_mul_full(Xf(1000+i), g)
        factor = poly_add_full(Cf(1), poly_neg_full(zg))
        p = poly_mul_full(p, factor)
    return p

# Sum: ∑G_i²
def sumPoly(n):
    p = {}
    for i in range(n):
        g = gadget(i)
        p = poly_add_full(p, poly_mul_full(g, g))
    return p

# TM compiled: ∑(q_t · G_t)²
def tmPoly(n):
    p = {}
    for t in range(n):
        g = gadget(t)
        qg = poly_mul_full(Xf(3000+t), g)
        p = poly_add_full(p, poly_mul_full(qg, qg))
    return p

print("=" * 60)
print("BOOLEAN FUNCTION COMPARISON")
print("=" * 60)

# For n=3: enumerate all boolean inputs and compare values
n = 3
pp = productPoly(n)
sp = sumPoly(n)
tp = tmPoly(n)

x_vars = list(range(2*n))
z_vars = list(range(1000, 1000+n))
q_vars = list(range(3000, 3000+n))

print(f"\nn={n}: Evaluating on boolean inputs")
print("(Satisfying: exactly one of x_{2i},x_{2i+1} = 1 per clause)")
print()

# Product needs z_i values too. Set z_i = 1 for all i.
print("--- Product ∏(1-G_i) [z=1] vs Sum ∑G² vs TM ∑(q·G)² [q=1] ---")
print(f"{'x':>15} {'clause_sat':>10} {'product':>10} {'sum':>10} {'tm':>10}")

match_count = 0
total = 0
for bits in cartprod([0,1], repeat=2*n):
    assignment_x = {i: bits[i] for i in range(2*n)}
    
    # Check which clauses satisfied
    clause_sat = all(bits[2*i]+bits[2*i+1] == 1 for i in range(n))
    
    # Product with z=1
    a_prod = dict(assignment_x)
    for i in range(n): a_prod[1000+i] = 1
    pv = eval_full(pp, a_prod)
    
    # Sum
    sv = eval_full(sp, assignment_x)
    
    # TM with q=1
    a_tm = dict(assignment_x)
    for t in range(n): a_tm[3000+t] = 1
    tv = eval_full(tp, a_tm)
    
    total += 1
    bits_str = ''.join(str(b) for b in bits)
    print(f"{bits_str:>15} {str(clause_sat):>10} {pv:>10} {sv:>10} {tv:>10}")
    
    # Check: product=0 iff NOT all satisfied? No: product=0 iff any G_i=1/z_i
    # With z=1: product = ∏(1-G_i) = 0 iff any G_i=1
    # G_i = x_{2i}+x_{2i+1}-1 = 0 when clause satisfied (sum=1)
    # G_i = 1 when both x=1, G_i = -1 when both x=0
    # Product = 0 iff any G_i ∈ {-1, 1} with z=1... 
    # Actually product = ∏(1-G_i): 1-G_i = 1-(x_a+x_b-1) = 2-x_a-x_b
    # = 2 when both 0, = 1 when one 1, = 0 when both 1

print(f"\nNote: Product=0 when any clause has BOTH vars=1 (both true)")
print(f"Sum=0 when ALL clauses satisfied (G_i=0 for all i)")
print(f"TM=0 when ALL clauses satisfied (q=1, G_i=0)")
print()
print("Product and Sum encode DIFFERENT functions over integers!")
print("They only agree on satisfiability in a weak sense.")
print()

# KEY: What boolean function does each encode?
print("=== SATISFIABILITY ENCODING ===")
print("Sum = 0  ⟺  all clauses satisfied")
print("Product|z=1 = 0  ⟺  some clause has both vars = 1")
print("These are DIFFERENT conditions!")
print()
print("The verifier polynomial ∏(1-z_C·G_C) is meant to be")
print("nonzero on satisfying assignments (with appropriate z),")
print("not zero. The SPDP rank measures the 'complexity' of")
print("this nonzero-ness, not the zero set.")
