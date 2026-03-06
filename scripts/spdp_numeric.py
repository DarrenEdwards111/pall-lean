#!/usr/bin/env python3
"""Numeric SPDP rank via finite field evaluation.

Evaluate derivatives at random points over a large prime field.
Rank of the evaluation matrix = SPDP rank (generically).
"""
from itertools import combinations
import numpy as np
from functools import lru_cache

P = 10007  # prime for modular arithmetic

def mod(x): return x % P

class MPoly:
    """Multivariate polynomial over Z/pZ as dict: exponent_tuple -> coeff."""
    def __init__(self, n, terms=None):
        self.n = n
        self.terms = terms or {}
    
    @staticmethod
    def var(n, i):
        e = [0]*n; e[i] = 1
        return MPoly(n, {tuple(e): 1})
    
    @staticmethod
    def const(n, c):
        return MPoly(n, {tuple([0]*n): mod(c)})
    
    def __add__(self, other):
        r = dict(self.terms)
        for e, c in other.terms.items():
            r[e] = mod(r.get(e, 0) + c)
            if r[e] == 0: del r[e]
        return MPoly(self.n, r)
    
    def __sub__(self, other):
        r = dict(self.terms)
        for e, c in other.terms.items():
            r[e] = mod(r.get(e, 0) - c)
            if r[e] == 0: del r[e]
        return MPoly(self.n, r)
    
    def __mul__(self, other):
        r = {}
        for e1, c1 in self.terms.items():
            for e2, c2 in other.terms.items():
                e = tuple(a+b for a,b in zip(e1, e2))
                r[e] = mod(r.get(e, 0) + c1*c2)
                if e in r and r[e] == 0: del r[e]
        return MPoly(self.n, r)
    
    def pderiv(self, i):
        r = {}
        for e, c in self.terms.items():
            if e[i] > 0:
                ne = list(e); ne[i] -= 1
                nc = mod(c * e[i])
                ne = tuple(ne)
                r[ne] = mod(r.get(ne, 0) + nc)
                if ne in r and r[ne] == 0: del r[ne]
        return MPoly(self.n, r)
    
    def eval_at(self, pt):
        """Evaluate at point pt (list of ints mod P)."""
        s = 0
        for e, c in self.terms.items():
            v = c
            for i, ei in enumerate(e):
                if ei > 0: v = mod(v * pow(pt[i], ei, P))
            s = mod(s + v)
        return s
    
    def is_zero(self): return len(self.terms) == 0

def iterderiv(poly, indices):
    p = poly
    for i in indices:
        p = p.pderiv(i)
        if p.is_zero(): return p
    return p

N = 12  # total vars: x0..x8 clause, x9..x11 selectors
ONE = MPoly.const(N, 1)
X = [MPoly.var(N, i) for i in range(N)]

def g(i):
    return (ONE - X[3*i]) * (ONE - X[3*i+1]) * (ONE - X[3*i+2])

def g2(i):
    gi = g(i)
    return gi * gi

z = [X[9], X[10], X[11]]

def compute_rank(poly, kappa, var_indices):
    """Compute rank by evaluating derivatives at random points."""
    rng = np.random.RandomState(42)
    
    # Collect nonzero derivative indices
    deriv_combos = list(combinations(var_indices, kappa))
    
    # Evaluate each derivative at multiple random points
    n_points = 30
    rows = []
    for S in deriv_combos:
        d = iterderiv(poly, S)
        if d.is_zero(): continue
        row = []
        for _ in range(n_points):
            pt = [int(rng.randint(1, P)) for _ in range(N)]
            row.append(d.eval_at(pt))
        rows.append(row)
    
    if not rows: return 0
    mat = np.array(rows, dtype=np.int64)
    # Rank over finite field ≈ rank of numeric matrix (for large P)
    return int(np.linalg.matrix_rank(mat.astype(float)))

print("Building polynomials...")

forms = {}
forms["∏(1-z·G)"] = (ONE-z[0]*g(0)) * (ONE-z[1]*g(1)) * (ONE-z[2]*g(2))
forms["Σ G²"] = g2(0) + g2(1) + g2(2)

print("Building product forms...")
forms["∏(1-z·G²)"] = (ONE-z[0]*g2(0)) * (ONE-z[1]*g2(1)) * (ONE-z[2]*g2(2))
forms["∏(1+z·G²)"] = (ONE+z[0]*g2(0)) * (ONE+z[1]*g2(1)) * (ONE+z[2]*g2(2))
forms["(∏z)·ΣG²"] = z[0]*z[1]*z[2] * (g2(0)+g2(1)+g2(2))
forms["Σ z·G²"] = z[0]*g2(0) + z[1]*g2(1) + z[2]*g2(2)

cv = list(range(9))
v12 = list(range(12))

print(f"\n{'Form':<20} {'κ=1':>5} {'κ=2':>5} {'κ=3':>5} {'κ=4':>5}")
print("-"*40)

var_map = {
    "Σ G²": cv,
}

for name, poly in forms.items():
    vi = cv if name == "Σ G²" else v12
    rs = []
    for k in range(1, 5):
        r = compute_rank(poly, k, vi)
        rs.append(r)
    print(f"{name:<20} {rs[0]:>5} {rs[1]:>5} {rs[2]:>5} {rs[3]:>5}")
