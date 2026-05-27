"""
Exact SPDP-rank toolkit (shifted partial-derivative polynomial rank).

Implements the rank measure of the P-vs-NP paper, Definition 17 / 52:

    Gamma_{kappa,ell}(p) = rank_F  M_{kappa,ell}(p),

where M has

    rows    : pairs (S, m) with S a kappa-subset of a chosen derivative pool,
              and m a shift monomial of total degree <= ell;
              the row is the coefficient vector of   m * d_S(p)
              where d_S = product over i in S of  d/dx_i   (each first order).
    columns : every monomial that occurs in any row, in the standard monomial
              basis (no x_i^2 = x_i reduction -- we work over the full
              polynomial ring so the permanent validation is exact).

Rank is computed exactly over Q via sympy.

This file makes no claim either way about P vs NP; it is an instrument for
*measuring* SPDP rank of concrete polynomials, so that claims can be checked
rather than asserted.
"""

from __future__ import annotations
import itertools
from sympy import Poly, Integer, Matrix, diff, expand


def _all_monomials_leq(all_vars, max_deg):
    """All exponent tuples over all_vars with total degree <= max_deg."""
    n = len(all_vars)
    if max_deg == 0:
        yield (0,) * n
        return
    # stars and bars over n vars with total degree d, for d = 0..max_deg
    for d in range(max_deg + 1):
        for combo in _compositions(d, n):
            yield combo


def _compositions(total, parts):
    """All nonneg integer tuples of length `parts` summing to `total`."""
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in _compositions(total - first, parts - 1):
            yield (first,) + rest


def _poly_coeff_dict(expr, all_vars):
    """monomial-exponent-tuple -> rational coefficient."""
    expr = expand(expr)
    if expr == 0:
        return {}
    p = Poly(expr, *all_vars)
    return {tuple(mono): coeff for mono, coeff in p.terms()}


def spdp_matrix(p, all_vars, kappa, ell, deriv_pool=None):
    """
    Build M_{kappa,ell}(p).

    p          : sympy expression (a polynomial in all_vars)
    all_vars   : ordered list of every variable (defines the monomial basis)
    kappa      : size of derivative set S
    ell        : maximum shift-monomial degree
    deriv_pool : variables S is drawn from (default: all_vars)

    Returns (Matrix, rows_meta) where rows_meta lists (S, shift_monomial).
    """
    if deriv_pool is None:
        deriv_pool = list(all_vars)

    shift_monos = list(_all_monomials_leq(all_vars, ell))

    rows = []          # each row is a coeff dict
    rows_meta = []
    col_index = {}     # monomial tuple -> column id
    columns = []

    for S in itertools.combinations(deriv_pool, kappa):
        dpS = p
        for v in S:
            dpS = diff(dpS, v)
        dpS = expand(dpS)
        if dpS == 0:
            # still record empty rows (rank contribution zero) for honesty
            for m_exp in shift_monos:
                rows.append({})
                rows_meta.append((S, m_exp))
            continue
        for m_exp in shift_monos:
            m = Integer(1)
            for v, e in zip(all_vars, m_exp):
                m *= v ** e
            cd = _poly_coeff_dict(m * dpS, all_vars)
            for mono in cd:
                if mono not in col_index:
                    col_index[mono] = len(columns)
                    columns.append(mono)
            rows.append(cd)
            rows_meta.append((S, m_exp))

    ncols = len(columns)
    if ncols == 0:
        return Matrix.zeros(len(rows), 1), rows_meta

    M = Matrix.zeros(len(rows), ncols)
    for r, cd in enumerate(rows):
        for mono, coeff in cd.items():
            M[r, col_index[mono]] = coeff
    return M, rows_meta


def spdp_rank(p, all_vars, kappa, ell, deriv_pool=None):
    M, _ = spdp_matrix(p, all_vars, kappa, ell, deriv_pool=deriv_pool)
    return M.rank()


def num_monomials_leq(num_vars, max_deg):
    """#monomials in num_vars variables of total degree <= max_deg."""
    from math import comb
    return sum(comb(d + num_vars - 1, num_vars - 1) for d in range(max_deg + 1))
