#!/usr/bin/env python3
"""
SPDP rank for hybrid product-of-local-blocks forms.

Test various compiler normal forms to find one with BOTH:
- Superpolynomial rank (NP-side extraction works)
- Some locality/collapse property (P-side bound provable)

Forms tested:
1. ∏ H_b  (pure product of local blocks)
2. Y · ∏ H_b  (padded product)
3. ∏_b (1 + local_b)  (product of near-identity blocks)
4. Y · ∏_b (Σ_{c∈b} G_c²)  (product of local sums)
5. Block-grouped: ∏_{groups} (Σ_{c∈group} G_c²)
6. Mixed: Y · (∏ selectors) · (Σ G²)  -- selectors multiplicative, constraints additive

Key question: is there a form where rank grows superpolynomially
but a width/locality argument still gives a polynomial upper bound?
"""

from itertools import combinations
from sympy import symbols, expand, diff
import numpy as np

xs = symbols('x0:18')  # generous variable space

def clause_gadget(i):
    """(1-x_{3i})(1-x_{3i+1})(1-x_{3i+2})"""
    return (1 - xs[3*i]) * (1 - xs[3*i+1]) * (1 - xs[3*i+2])

def deriv_list(poly, var_indices):
    p = expand(poly)
    for v in var_indices:
        p = diff(p, xs[v])
        if p == 0:
            return 0
    return expand(p)

def compute_rank(poly, kappa, var_indices, all_vars):
    from sympy import Poly as SPoly
    derivatives = []
    for S in combinations(var_indices, kappa):
        d = deriv_list(poly, S)
        if d != 0:
            derivatives.append(d)
    
    if not derivatives:
        return 0
    
    all_monoms = set()
    vecs = []
    for d in derivatives:
        p = SPoly(d, *all_vars)
        v = {m: c for m, c in zip(p.monoms(), p.coeffs())}
        vecs.append(v)
        all_monoms.update(v.keys())
    
    all_monoms = sorted(all_monoms)
    monom_idx = {m: i for i, m in enumerate(all_monoms)}
    
    mat = np.zeros((len(vecs), len(all_monoms)), dtype=float)
    for i, v in enumerate(vecs):
        for m, c in v.items():
            mat[i, monom_idx[m]] = float(c)
    
    return int(np.linalg.matrix_rank(mat))

# Setup: 4 disjoint clauses
g = [clause_gadget(i) for i in range(4)]
n_clause_vars = 12
z = [xs[12], xs[13], xs[14], xs[15]]  # selectors
y = [xs[16], xs[17]]  # padding

print("=" * 70)
print("SPDP Rank: Hybrid Normal Form Search")
print("4 disjoint clauses, vars x0..x11, selectors z12..z15, pad y16,y17")
print("=" * 70)

# Form 1: Pure product ∏(1-z_c·G_c)
P1 = expand(1)
for i in range(4):
    P1 = expand(P1 * (1 - z[i] * g[i]))
print("\n--- Form 1: ∏(1-z_c·G_c) [pure Tseitin product] ---")
vars1 = list(range(16))
all1 = list(xs[:16])
for k in range(1, 6):
    r = compute_rank(P1, k, vars1, all1)
    print(f"  κ={k}: rank = {r}")

# Form 2: Σ G_c² [pure sum of squares]
P2 = sum(expand(gi**2) for gi in g)
print("\n--- Form 2: Σ G_c² [pure violation] ---")
vars2 = list(range(12))
all2 = list(xs[:12])
for k in range(1, 6):
    r = compute_rank(P2, k, vars2, all2)
    print(f"  κ={k}: rank = {r}")

# Form 3: Y · Σ G² [padded violation, like compiler]
Y = xs[16] * xs[17]
P3 = expand(Y * P2)
print("\n--- Form 3: Y · Σ G² [padded violation] ---")
vars3 = list(range(12)) + [16, 17]
all3 = list(xs[:12]) + [xs[16], xs[17]]
for k in range(1, 6):
    r = compute_rank(P3, k, vars3, all3)
    print(f"  κ={k}: rank = {r}")

# Form 4: ∏_c (1 + G_c²) [product of 1+local-square]
P4 = expand(1)
for i in range(4):
    P4 = expand(P4 * (1 + expand(g[i]**2)))
print("\n--- Form 4: ∏(1 + G_c²) [product of near-identity local blocks] ---")
for k in range(1, 6):
    r = compute_rank(P4, k, vars2, all2)
    print(f"  κ={k}: rank = {r}")

# Form 5: ∏_c (1 - G_c²) [product, penalty version]
P5 = expand(1)
for i in range(4):
    P5 = expand(P5 * (1 - expand(g[i]**2)))
print("\n--- Form 5: ∏(1 - G_c²) [product of 1-square] ---")
for k in range(1, 6):
    r = compute_rank(P5, k, vars2, all2)
    print(f"  κ={k}: rank = {r}")

# Form 6: (∏ z_c) · (Σ G_c²) [selector product × violation sum]
P6 = expand(z[0]*z[1]*z[2]*z[3] * P2)
print("\n--- Form 6: (∏ z_c) · Σ G² [selector product × violation] ---")
vars6 = list(range(16))
all6 = list(xs[:16])
for k in range(1, 6):
    r = compute_rank(P6, k, vars6, all6)
    print(f"  κ={k}: rank = {r}")

# Form 7: Σ_c z_c · G_c² [selector-weighted sum]
P7 = sum(expand(z[i] * g[i]**2) for i in range(4))
print("\n--- Form 7: Σ z_c·G_c² [selector-weighted violation] ---")
for k in range(1, 6):
    r = compute_rank(P7, k, vars6, all6)
    print(f"  κ={k}: rank = {r}")

# Form 8: ∏_c (1 - z_c · G_c²) [product with squared gadgets]
P8 = expand(1)
for i in range(4):
    P8 = expand(P8 * (1 - z[i] * expand(g[i]**2)))
print("\n--- Form 8: ∏(1 - z_c·G_c²) [product, squared gadgets] ---")
for k in range(1, 6):
    r = compute_rank(P8, k, vars6, all6)
    print(f"  κ={k}: rank = {r}")

# Form 9: Fuzzy hybrid: ∏_c (α + β·G_c²) with α=1, β=1
# This is ∏(1+G²) but let's also try with selectors
P9 = expand(1)
for i in range(4):
    P9 = expand(P9 * (1 + z[i] * expand(g[i]**2)))
print("\n--- Form 9: ∏(1 + z_c·G_c²) [fuzzy product-of-selected-squares] ---")
for k in range(1, 6):
    r = compute_rank(P9, k, vars6, all6)
    print(f"  κ={k}: rank = {r}")

print("\n" + "=" * 70)
print("COMPARISON SUMMARY")
print("=" * 70)
print(f"{'Form':<45} {'κ=1':>5} {'κ=2':>5} {'κ=3':>5} {'κ=4':>5} {'κ=5':>5}")
print("-" * 70)

forms = {
    "1. ∏(1-z·G) [product]": (P1, vars1, all1),
    "2. Σ G² [sum-of-squares]": (P2, vars2, all2),
    "3. Y·Σ G² [padded violation]": (P3, vars3, all3),
    "4. ∏(1+G²) [prod near-id]": (P4, vars2, all2),
    "5. ∏(1-G²) [prod penalty]": (P5, vars2, all2),
    "6. (∏z)·Σ G² [sel×viol]": (P6, vars6, all6),
    "7. Σ z·G² [weighted sum]": (P7, vars6, all6),
    "8. ∏(1-z·G²) [prod sq gadget]": (P8, vars6, all6),
    "9. ∏(1+z·G²) [fuzzy hybrid]": (P9, vars6, all6),
}

for name, (poly, vi, av) in forms.items():
    ranks = []
    for k in range(1, 6):
        ranks.append(compute_rank(poly, k, vi, av))
    print(f"{name:<45} {ranks[0]:>5} {ranks[1]:>5} {ranks[2]:>5} {ranks[3]:>5} {ranks[4]:>5}")
