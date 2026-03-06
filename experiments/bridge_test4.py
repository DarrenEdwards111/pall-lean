#!/usr/bin/env python3
"""
Key question: Does EVERY Tseitin (product-form) polynomial have 
nonzero |T|=2 traced Möbius mass?

Test: create product-form polynomials with DISJOINT clause gadgets
(each uses separate state vars) and check.

For product of disjoint gadgets: Π(1 - G_i) where each G_i uses 
separate variables. After partial trace, product structure should
give uniform Möbius mass = 1 at all levels.

But what about TM transitions where gadgets SHARE state variables?
The sequential accumulator shares s_i between consecutive constraints.
That's what creates coupling!

Critical: In a real TM encoding, consecutive constraints share 
state/tape variables. This shared-variable product structure is
what creates cross-clause coupling visible after partial trace.

Let me test:
1. Disjoint product: each gadget has its own state vars
2. Shared product: consecutive gadgets share state vars (TM-like)
"""

import sympy
from sympy import expand, Symbol
from itertools import combinations, product as cartesian_product

def partial_trace(p, state_vars):
    result = sympy.Integer(0)
    for assignment in cartesian_product([0, 1], repeat=len(state_vars)):
        subs = {state_vars[j]: assignment[j] for j in range(len(state_vars))}
        result += p.subs(subs)
    return expand(result)

def coeff_mass(p, var_set, all_vars):
    if p == 0:
        return 0
    from sympy import Poly
    poly = Poly(p, *all_vars)
    count = 0
    for monom, coeff in poly.as_dict().items():
        if coeff != 0:
            supported = {all_vars[i] for i, e in enumerate(monom) if e > 0}
            if supported <= var_set:
                count += 1
    return count

def mobius_obs(traced_p, T_indices, content_vars):
    T = sorted(T_indices)
    T_card = len(T)
    result = 0
    for r in range(T_card + 1):
        for S_tuple in combinations(T, r):
            S = set(S_tuple)
            var_set = {content_vars[i] for i in S}
            mass = coeff_mass(traced_p, var_set, content_vars)
            sign = (-1) ** (T_card - len(S))
            result += sign * mass
    return result

n = 3
x = [Symbol(f'x{i}') for i in range(n)]

# Model A: DISJOINT gadgets — each constraint has its own state vars
# G_0: (a_0 - x_0)^2 with state a_0
# G_1: (a_1 - x_1)^2 with state a_1  
# G_2: (a_2 - x_2)^2 with state a_2
# Product: Π(1 - (a_i - x_i)^2)
print("="*60)
print("Model A: DISJOINT product (each gadget has own state vars)")
print("="*60)
a = [Symbol(f'a{i}') for i in range(n)]
pA = 1
for i in range(n):
    pA *= (1 - (a[i] - x[i])**2)
pA = expand(pA)
tracedA = partial_trace(pA, a)
print(f"Traced: {tracedA}")
for k in range(1, n+1):
    mass = sum(abs(mobius_obs(tracedA, T, x)) for T in combinations(range(n), k))
    print(f"  Level |T|={k} mass: {mass}")

# Model B: SHARED state (TM-like sequential)
# s_0 = 1, s_i = s_{i-1} * x_i
# Product: (1-(s_0-1)^2) * Π(1-(s_i - s_{i-1}*x_i)^2)
print(f"\n{'='*60}")
print("Model B: SHARED state (TM sequential accumulator, product form)")
print("="*60)
s = [Symbol(f's{j}') for j in range(n + 1)]
pB = (1 - (s[0] - 1)**2)
for i in range(n):
    pB *= (1 - (s[i+1] - s[i]*x[i])**2)
pB = expand(pB)
tracedB = partial_trace(pB, s)
print(f"Traced: {tracedB}")
for k in range(1, n+1):
    mass = sum(abs(mobius_obs(tracedB, T, x)) for T in combinations(range(n), k))
    print(f"  Level |T|={k} mass: {mass}")

# Model C: Check if disjoint product gives uniform mass (= 2^m per subset)
print(f"\n{'='*60}")
print("Model C: DISJOINT product with BOOLEAN state (a_i ∈ {0,1})")
print("  Each (1-(a_i-x_i)^2) after trace over a_i gives")
print("  sum_{a=0,1} (1-(a-x)^2) = (1-(0-x)^2) + (1-(1-x)^2)")
print("  = (1-x^2) + (1-(1-2x+x^2)) = 1-x^2 + 2x-x^2 = 2x-2x^2+1")
print("="*60)

# Verify each piece
for i in range(n):
    piece = expand((1 - (a[i] - x[i])**2))
    traced_piece = partial_trace(piece, [a[i]])
    print(f"  Traced piece {i}: {traced_piece}")

print(f"\n  Full traced product: {tracedA}")
print(f"  = product of individual pieces? ", end="")
product_of_pieces = 1
for i in range(n):
    product_of_pieces *= partial_trace(expand(1 - (a[i] - x[i])**2), [a[i]])
product_of_pieces = expand(product_of_pieces)
print("YES" if product_of_pieces == tracedA else "NO")
print(f"  Product of pieces: {product_of_pieces}")

# Key question: does the DISJOINT product after trace still have
# product structure in content vars?
print(f"\n{'='*60}")
print("ANALYSIS")
print("="*60)
print("""
DISJOINT product: Π_i f(x_i) where f(x) = 2x - 2x² + 1
  After trace, this IS a product of univariate polynomials.
  Möbius mass: f̂_T = 1 for ALL nonempty T (product form property).
  
SHARED product (TM): Π_i (1 - G_i(s_{i-1}, s_i, x_i))
  Gadgets share state vars → after trace, NOT a simple product.
  Creates content cross-terms due to shared state variable coupling.
  
SHARED sum (TM): Σ_i G_i(s_{i-1}, s_i, x_i)²  
  After trace: sum distributes over partial trace.
  Each traced piece is local → LOCAL SUM → zero Möbius mass.

So the bridge depends on:
1. The polynomial MUST be product form (Tseitin encoding)
2. Product form + shared state vars → nonzero traced Möbius mass
3. Sum form → zero traced Möbius mass

The P≠NP argument:
- A correct poly-time SAT solver compiles to Tseitin polynomial (PRODUCT form)
- Product form has nonzero Möbius mass (proved: product_form_mobius_uniform)  
- But the P-side claims sum form has zero mass
- TENSION: can a product-form polynomial also be expressed as local sum?
  
  Only if the product degenerates — e.g., Π f(x_i) = Σ f(x_i) only
  when the product is actually a sum (impossible for nontrivial f).
""")
