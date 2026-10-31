#!/usr/bin/env python3
"""Exact-definition SPDP rank at small n, for the Phase-1 obstruction tests.

Conventions implemented (both appear in the project):
  LEAN  = MultilinearSPDP.mlBlockedSpdpSubspace (pall-lean main 7f53946):
          rows mlProj(m * d^S p), S an ordered Nodup list with |S| = kappa
          (strict), block-admissible (<=1 var per block), m a monomial with
          totalDegree <= ell AND vars(m) subset of S ("Lemma 18" restriction);
          mlProj DROPS every non-multilinear monomial (Finsupp.filter).
  PAPER = Definition 12 of 'P vs NP Paper.pdf' (arXiv 2512.11820v5):
          rows u * d^tau p, |tau| = kappa, block support <= kappa, u ANY
          monomial of degree <= ell; columns multilinear monomials.  The paper
          says the ambient space is taken modulo <x_i^2 - x_i>; we implement
          that reading ('reduce': x_i^2 -> x_i).  (Reading it as 'drop' is the
          LEAN mlProj behaviour; we also report PAPER-drop.)
Field: rank computed modulo the prime 2^31-1 (a lower bound for the rank over
Q, equal to it unless the prime divides a minor; values were spot-checked
against exact Fraction elimination for the small cases, see --exact).
Block partition: singleton blocks (this is `compilerBlockPartition`, assign = id),
unless --pairs is given.
Polynomials are multilinear, represented as {frozenset(vars): coeff}.
"""
import itertools, math, sys, json
from fractions import Fraction
P = 2**31 - 1

def deriv(p, i):
    return {m - {i}: c for m, c in p.items() if i in m}

def deriv_set(p, S):
    for i in S:
        p = deriv(p, i)
        if not p: break
    return p

def mul_mono(p, u, mode):
    """u: tuple of variable indices with multiplicity (a monomial)."""
    out = {}
    uset = set(u)
    u_ml = len(uset) == len(u)
    for m, c in p.items():
        if mode == 'drop':
            if not u_ml or (m & uset):
                continue
            k = m | uset
        else:  # reduce x^2 -> x
            k = m | uset
        k = frozenset(k)
        out[k] = out.get(k, 0) + c
    return {k: v for k, v in out.items() if v}

def monomials_upto(vars_, deg):
    for d in range(deg + 1):
        for u in itertools.combinations_with_replacement(vars_, d):
            yield u

class Basis:
    def __init__(self, exact=False):
        self.piv = {}; self.exact = exact
    def add(self, row):
        r = {k: (Fraction(v) if self.exact else v % P) for k, v in row.items()}
        r = {k: v for k, v in r.items() if v}
        while r:
            k = min(r, key=lambda m: (len(m), sorted(m)))
            if k in self.piv:
                b = self.piv[k]; f = r[k]
                for kk, vv in b.items():
                    nv = r.get(kk, 0) - f * vv
                    if not self.exact: nv %= P
                    if nv: r[kk] = nv
                    else: r.pop(kk, None)
            else:
                inv = (1 / r[k]) if self.exact else pow(r[k], P - 2, P)
                self.piv[k] = {kk: (vv * inv if self.exact else vv * inv % P) for kk, vv in r.items()}
                return True
        return False
    def rank(self): return len(self.piv)

def spdp_rank(p, n, kappa, ell, conv='LEAN', mode='drop', blocks=None, exact=False, cap=None):
    blocks = blocks or list(range(n))
    B = Basis(exact)
    rows = 0
    for S in itertools.combinations(range(n), kappa):  # order irrelevant: derivatives commute
        if len({blocks[i] for i in S}) < kappa:
            continue
        d = deriv_set(p, S)
        if not d: continue
        shift_vars = S if conv == 'LEAN' else range(n)
        for u in monomials_upto(list(shift_vars), ell):
            q = mul_mono(d, u, mode)
            rows += 1
            if q: B.add(q)
            if cap and B.rank() >= cap: return B.rank(), rows
    return B.rank(), rows

# ---- test polynomials (all multilinear over Q) ----
def p_prod(n):            # x1...xn  (AND), n-1 multiplications
    return {frozenset(range(n)): 1}
def p_esym(n, d):         # elementary symmetric e_{n,d}
    return {frozenset(c): 1 for c in itertools.combinations(range(n), d)}
def p_point(n, a=None):   # indicator of a point a in {0,1}^n (multilinear)
    a = a or [1 if i % 2 == 0 else 0 for i in range(n)]
    poly = {frozenset(): 1}
    for i in range(n):
        fac = {frozenset([i]): 1} if a[i] else {frozenset(): 1, frozenset([i]): -1}
        new = {}
        for m1, c1 in poly.items():
            for m2, c2 in fac.items():
                k = m1 | m2; new[k] = new.get(k, 0) + c1 * c2
        poly = {k: v for k, v in new.items() if v}
    return poly
def p_parity(n):          # multilinear extension of XOR: (1 - prod(1-2x_i))/2  -> integer-scaled by 2
    poly = {frozenset(): 1}
    for i in range(n):
        new = {}
        for m, c in poly.items():
            new[m] = new.get(m, 0) + c
            k = m | {i}; new[k] = new.get(k, 0) - 2 * c
        poly = {k: v for k, v in new.items() if v}
    poly = {k: -v for k, v in poly.items()}
    poly[frozenset()] = poly.get(frozenset(), 0) + 1
    return {k: v for k, v in poly.items() if v}   # = 2*parity; rank unchanged
def p_det(k):             # determinant of a k x k matrix of distinct variables (n = k^2)
    poly = {}
    for perm in itertools.permutations(range(k)):
        sgn = 1
        for i in range(k):
            for j in range(i + 1, k):
                if perm[i] > perm[j]: sgn = -sgn
        poly[frozenset(i * k + perm[i] for i in range(k))] = sgn
    return poly
def p_imm(d):             # (1,1) entry of a product of d generic 2x2 matrices, n = 4d
    # matrix t has vars 4t + (2r + c)
    vec = {0: {frozenset(): 1}, 1: {}}
    for t in range(d):
        new = {0: {}, 1: {}}
        for r in (0, 1):
            for c in (0, 1):
                v = 4 * t + 2 * r + c
                for m, co in vec[r].items():
                    k = m | {v}; new[c][k] = new[c].get(k, 0) + co
        vec = new
    return {k: v for k, v in vec[0].items() if v}

def run(exact=False):
    res = []
    def rec(name, n, p, kappa, ell, cheap):
        out = {'poly': name, 'n': n, 'kappa': kappa, 'ell': ell, 'circuit_size_note': cheap}
        for conv, mode in (('LEAN', 'drop'), ('PAPER', 'reduce'), ('PAPER', 'drop')):
            r, rows = spdp_rank(p, n, kappa, ell, conv, mode, exact=exact)
            out[f'{conv}-{mode}'] = r
        out['C(n,kappa)'] = math.comb(n, kappa)
        res.append(out); print(json.dumps(out), flush=True)
        json.dump(res, open(OUT, 'w'), indent=1)
    for n in range(4, 12):
        k = max(1, int(math.log2(n)))
        rec('prod x1..xn', n, p_prod(n), k, k, f'{n-1} AND gates')
        rec('parity (2*MLE)', n, p_parity(n), k, k, 'O(n) XOR gates')
        rec('point indicator', n, p_point(n), k, k, f'{n-1} AND + <= {n} NOT')
        if n <= 10: rec(f'e_(n,n/2)', n, p_esym(n, n // 2), k, k, 'O(n^2) arithmetic (DP)')
    for n in range(4, 11, 2):
        rec('prod x1..xn [kappa=n/2, ell=0]', n, p_prod(n), n // 2, 0, f'{n-1} AND gates')
    for kk in (2, 3):
        n = kk * kk; k = max(1, int(math.log2(n)))
        rec(f'det_{kk}', n, p_det(kk), k, k, 'poly-size (Berkowitz)')
    for d in (2, 3):
        n = 4 * d; k = max(1, int(math.log2(n)))
        rec(f'IMM 2x2 x{d} entry(1,1)', n, p_imm(d), k, k, f'{8*d} mults')
    return res

OUT = 'results.json'
if __name__ == '__main__':
    if len(sys.argv) > 1 and not sys.argv[1].startswith('--'): OUT = sys.argv[1]
    exact = '--exact' in sys.argv
    res = run(exact)
    json.dump(res, open(sys.argv[1] if len(sys.argv) > 1 and not sys.argv[1].startswith('--') else 'results.json', 'w'), indent=1)
