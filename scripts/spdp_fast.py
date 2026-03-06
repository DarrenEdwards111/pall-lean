#!/usr/bin/env python3
"""Fast SPDP rank test: 3 disjoint clauses, 9 clause vars + 3 selectors."""
from itertools import combinations
from sympy import symbols, expand, diff, Poly
import numpy as np

xs = symbols('x0:15')

def g(i): return (1-xs[3*i])*(1-xs[3*i+1])*(1-xs[3*i+2])
def g2(i): return expand(g(i)**2)

def rank(poly, kappa, vidx, avars):
    derivs = []
    for S in combinations(vidx, kappa):
        p = expand(poly)
        for v in S:
            p = diff(p, xs[v])
            if p == 0: break
        if p != 0: derivs.append(p)
    if not derivs: return 0
    monoms = set()
    vecs = []
    for d in derivs:
        pp = Poly(d, *avars)
        v = dict(zip(pp.monoms(), pp.coeffs()))
        vecs.append(v); monoms.update(v.keys())
    monoms = sorted(monoms)
    mi = {m:i for i,m in enumerate(monoms)}
    mat = np.zeros((len(vecs), len(monoms)), dtype=float)
    for i, v in enumerate(vecs):
        for m, c in v.items(): mat[i, mi[m]] = float(c)
    return int(np.linalg.matrix_rank(mat))

z = [xs[9], xs[10], xs[11]]
cv = list(range(9)); av9 = list(xs[:9])
av12 = list(xs[:12]); v12 = list(range(12))

forms = {}

# 1. Product ∏(1-z·G)
forms["∏(1-z·G)"] = (expand((1-z[0]*g(0))*(1-z[1]*g(1))*(1-z[2]*g(2))), v12, av12)
# 2. Σ G²
forms["Σ G²"] = (g2(0)+g2(1)+g2(2), cv, av9)
# 3. ∏(1+G²)
forms["∏(1+G²)"] = (expand((1+g2(0))*(1+g2(1))*(1+g2(2))), cv, av9)
# 4. ∏(1-G²)
forms["∏(1-G²)"] = (expand((1-g2(0))*(1-g2(1))*(1-g2(2))), cv, av9)
# 5. ∏(1-z·G²)
forms["∏(1-z·G²)"] = (expand((1-z[0]*g2(0))*(1-z[1]*g2(1))*(1-z[2]*g2(2))), v12, av12)
# 6. ∏(1+z·G²)
forms["∏(1+z·G²)"] = (expand((1+z[0]*g2(0))*(1+z[1]*g2(1))*(1+z[2]*g2(2))), v12, av12)
# 7. (∏z)·ΣG²
forms["(∏z)·ΣG²"] = (expand(z[0]*z[1]*z[2]*(g2(0)+g2(1)+g2(2))), v12, av12)
# 8. Σ z·G²
forms["Σ z·G²"] = (expand(z[0]*g2(0)+z[1]*g2(1)+z[2]*g2(2)), v12, av12)
# 9. ∏(z+G²)
forms["∏(z+G²)"] = (expand((z[0]+g2(0))*(z[1]+g2(1))*(z[2]+g2(2))), v12, av12)

print(f"{'Form':<20} {'κ=1':>5} {'κ=2':>5} {'κ=3':>5} {'κ=4':>5}")
print("-"*40)
for name, (poly, vi, av) in forms.items():
    rs = [rank(poly, k, vi, av) for k in range(1,5)]
    print(f"{name:<20} {rs[0]:>5} {rs[1]:>5} {rs[2]:>5} {rs[3]:>5}")
