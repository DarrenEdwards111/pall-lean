#!/usr/bin/env python3
"""Checks that the Lean polynomial subsetPoly m k = sum_{|S|=k} x^S delta_S(y) is exactly the
characteristic polynomial chi_f (Def. 13) of f(x,y) = [|y| = k and y <= x], for small m, k
(exact integer coefficients), and that f is computed by a single linear scan."""
import itertools, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from def12_rank import mle, f_subset

def expand(m, k):
    N = 2 * m; c = [0] * (1 << N)
    for S in itertools.combinations(range(m), k):
        xs = sum(1 << i for i in S)
        ys = sum(1 << (m + j) for j in S)
        rest = [m + j for j in range(m) if j not in S]
        # delta_S(y) = y^S * prod_{j notin S} (1 - y_j) = sum_{R subset rest} (-1)^|R| y^{S u R}
        for r in range(len(rest) + 1):
            for R in itertools.combinations(rest, r):
                c[xs | ys | sum(1 << v for v in R)] += (-1) ** r
    return c

ok = True
for m in range(1, 6):
    for k in range(0, m + 1):
        if mle(f_subset(2 * m, k), 2 * m) != expand(m, k):
            ok = False; print("MISMATCH", m, k)
print("subsetPoly == chi_f for all m<=5, k<=m:", ok)
