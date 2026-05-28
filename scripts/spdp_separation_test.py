#!/usr/bin/env python3
"""
Empirical test: does SPDP rank (shifted partial derivatives) SEPARATE
easy from hard polynomials?

The honest, checkable algebraic mirror of "P vs NP" is "VP vs VNP", whose
canonical pair is:

    det_n   -- determinant   -- EASY  (in VP: Gaussian elimination / Berkowitz)
    perm_n  -- permanent      -- HARD  (VNP-complete; the algebraic NP-analogue)

They have IDENTICAL monomial support (sum over permutations of products
x_{i,sigma(i)}); they differ only by signs on coefficients.  So if the
SPDP-rank diagrams in the paper are right -- "P-side low rank, NP-side high
rank" -- then we MUST see rank(det) << rank(perm).  If instead they come out
equal, the measure does not track computational hardness.

Gamma_{k,l}(f) := dim < x^{<=l} . d^{=k} f >
  = rank of the matrix whose rows are { m * (d^alpha f) : |alpha|=k, deg m <= l }
    expressed over the monomial basis.

Rank is computed exactly over a large prime field (= rank over Q for all but
finitely many primes; we use a 31-bit Mersenne prime).
"""

import sympy as sp
import itertools
from itertools import combinations_with_replacement

PRIME = 2147483647  # 2^31 - 1, Mersenne prime


# ---------- linear algebra: exact rank over F_p ----------
def rank_mod_p(rows, p=PRIME):
    mat = [r[:] for r in rows]
    nrows = len(mat)
    if nrows == 0:
        return 0
    ncols = len(mat[0])
    pivot_row = 0
    rank = 0
    for col in range(ncols):
        piv = None
        for r in range(pivot_row, nrows):
            if mat[r][col] % p != 0:
                piv = r
                break
        if piv is None:
            continue
        mat[pivot_row], mat[piv] = mat[piv], mat[pivot_row]
        inv = pow(mat[pivot_row][col] % p, p - 2, p)
        mat[pivot_row] = [(x * inv) % p for x in mat[pivot_row]]
        prow = mat[pivot_row]
        for r in range(nrows):
            if r != pivot_row:
                f = mat[r][col] % p
                if f != 0:
                    mat[r] = [(a - f * b) % p for a, b in zip(mat[r], prow)]
        pivot_row += 1
        rank += 1
        if pivot_row == nrows:
            break
    return rank


# ---------- SPDP machinery ----------
def order_k_partials(f, vars, k):
    out = []
    n = len(vars)
    for combo in combinations_with_replacement(range(n), k):
        g = f
        for i in combo:
            g = sp.diff(g, vars[i])
        g = sp.expand(g)
        if g != 0:
            out.append(g)
    return out


def monomials_up_to(vars, maxdeg):
    mons = []
    n = len(vars)
    for d in range(maxdeg + 1):
        for combo in combinations_with_replacement(range(n), d):
            m = sp.Integer(1)
            for i in combo:
                m *= vars[i]
            mons.append(m)
    return mons


def spdp_rank(f, vars, k, l):
    f = sp.expand(f)
    partials = order_k_partials(f, vars, k)
    if not partials:
        return 0
    shifts = monomials_up_to(vars, l)
    poly_dicts = []
    monset = set()
    for p in partials:
        for s in shifts:
            q = sp.Poly(sp.expand(p * s), *vars)
            d = q.as_dict()
            poly_dicts.append(d)
            monset.update(d.keys())
    monlist = sorted(monset)
    idx = {m: j for j, m in enumerate(monlist)}
    rows = []
    for d in poly_dicts:
        row = [0] * len(monlist)
        for m, c in d.items():
            row[idx[m]] = int(c) % PRIME
        rows.append(row)
    return rank_mod_p(rows)


# ---------- the polynomials ----------
def make_matrix_vars(n):
    grid = [[sp.Symbol(f"x_{i}_{j}") for j in range(n)] for i in range(n)]
    flat = [grid[i][j] for i in range(n) for j in range(n)]
    return grid, flat


def det_poly(n, grid):
    return sp.expand(sp.Matrix(n, n, lambda i, j: grid[i][j]).det())


def perm_poly(n, grid):
    total = sp.Integer(0)
    for perm in itertools.permutations(range(n)):
        term = sp.Integer(1)
        for i in range(n):
            term *= grid[i][perm[i]]
        total += term
    return sp.expand(total)


def linform_pow(n, flat):
    """A genuinely simple polynomial of the same #vars and degree:
    (sum of all variables)^n.  Its order-k partials all lie in a single
    direction, so its SPDP rank should be MUCH smaller -- a control showing
    the measure is non-trivial (it CAN be small)."""
    s = sum(flat)
    return sp.expand(s ** n)


# ---------- run ----------
def run_for_n(n, configs):
    grid, flat = make_matrix_vars(n)
    nv = n * n
    det = det_poly(n, grid)
    perm = perm_poly(n, grid)
    lin = linform_pow(n, flat)
    print(f"\n=== n = {n}  ({nv} variables, degree {n}) ===")
    print(f"  det_{n} : {len(sp.Poly(det,*flat).as_dict())} monomials  (EASY / VP)")
    print(f"  perm_{n}: {len(sp.Poly(perm,*flat).as_dict())} monomials  (HARD / VNP-complete)")
    print(f"  (sum)^{n}: {len(sp.Poly(lin,*flat).as_dict())} monomials  (trivial control)")
    print(f"  {'(k,l)':>8} | {'rank det':>9} | {'rank perm':>9} | {'equal?':>6} | {'rank (sum)^n':>12}")
    print("  " + "-" * 60)
    for (k, l) in configs:
        rd = spdp_rank(det, flat, k, l)
        rp = spdp_rank(perm, flat, k, l)
        rl = spdp_rank(lin, flat, k, l)
        eq = "YES" if rd == rp else "no"
        print(f"  {str((k,l)):>8} | {rd:>9} | {rp:>9} | {eq:>6} | {rl:>12}")


if __name__ == "__main__":
    run_for_n(2, [(1, 0), (1, 1), (1, 2), (2, 1), (2, 2)])
    run_for_n(3, [(1, 0), (1, 1), (2, 0), (2, 1), (3, 0)])
