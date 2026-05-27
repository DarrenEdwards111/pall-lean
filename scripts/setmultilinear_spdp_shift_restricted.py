#!/usr/bin/env python3
"""Prototype: plain SPDP Gamma vs set-multilinear-aware Gamma on NW instances.

This is a finite calibration script (not an asymptotic proof).
It compares:
  1) plain shifted-partial derivative rank Gamma_{k,ell}
  2) a set-multilinear-aware variant where shifts are restricted to block-multilinear monomials
     (at most one variable from each point-block), matching NW's natural block partition.

We also print denominator-style lower-bound factors to show how the set-multilinear restriction
can tighten the depth-3 style bound.
"""

from __future__ import annotations

from itertools import combinations, product
from math import comb
from typing import Sequence

from sympy import Matrix, Poly, diff, expand, symbols


def monomial_exponents_le(num_vars: int, degree: int) -> list[tuple[int, ...]]:
    out: list[tuple[int, ...]] = []

    def rec(pos: int, rem: int, cur: list[int]) -> None:
        if pos == num_vars:
            out.append(tuple(cur))
            return
        for e in range(rem + 1):
            cur.append(e)
            rec(pos + 1, rem - e, cur)
            cur.pop()

    rec(0, degree, [])
    return out


def monomial(vars_: Sequence, exp: Sequence[int]):
    t = 1
    for x, e in zip(vars_, exp):
        if e:
            t *= x**e
    return t


def nw_design_polynomial(q: int, degree: int, coeff_count: int):
    if degree > q:
        raise ValueError("prime-field model requires degree <= q")

    vars_ = symbols(f"y0:{degree*q}")

    def y(i: int, a: int):
        return vars_[i * q + a]

    total = 0
    for coeffs in product(range(q), repeat=coeff_count):
        term = 1
        for i in range(degree):
            value = sum(c * pow(i, power, q) for power, c in enumerate(coeffs)) % q
            term *= y(i, value)
        total += term
    return expand(total), vars_


def spdp_rank_with_shifts(poly, vars_, kappa: int, shifts: list[tuple[int, ...]]) -> int:
    rows = []
    shift_monos = [monomial(vars_, e) for e in shifts]

    for deriv_vars in combinations(vars_, kappa):
        p = poly
        for x in deriv_vars:
            p = diff(p, x)
            if p == 0:
                break
        if p == 0:
            continue
        for s in shift_monos:
            rows.append(expand(s * p))

    if not rows:
        return 0

    monoms = set()
    row_dicts = []
    for r in rows:
        coeffs = Poly(r, *vars_, domain="QQ").as_dict()
        row_dicts.append(coeffs)
        monoms.update(coeffs)

    basis = sorted(monoms)
    mat = [[d.get(m, 0) for m in basis] for d in row_dicts]
    return int(Matrix(mat).rank())


def set_multilinear_shifts_nw(d: int, q: int, ell: int) -> list[tuple[int, ...]]:
    """Shifts with at most one variable from each point-block.

    Blocks: B_i = {y_{i,0},...,y_{i,q-1}}.
    Shift degree <= ell, multilinear, and <=1 variable chosen per block.
    """
    n = d * q
    exps: list[tuple[int, ...]] = []

    for t in range(ell + 1):
        for blocks in combinations(range(d), t):
            for vals in product(range(q), repeat=t):
                e = [0] * n
                for b, v in zip(blocks, vals):
                    e[b * q + v] = 1
                exps.append(tuple(e))

    return exps


def plain_shift_count(num_vars: int, ell: int) -> int:
    return comb(num_vars + ell, ell)


def setml_shift_count_nw(d: int, q: int, ell: int) -> int:
    return sum(comb(d, t) * (q**t) for t in range(ell + 1))


def report_case(name: str, poly, vars_, d: int, q: int, degree: int, params):
    print("\n" + "=" * 86)
    print(name)
    print("=" * 86)
    num_vars = len(vars_)

    for kappa, ell in params:
        plain_shifts = monomial_exponents_le(num_vars, ell)
        setml_shifts = set_multilinear_shifts_nw(d, q, ell)

        gamma_plain = spdp_rank_with_shifts(poly, vars_, kappa, plain_shifts)
        gamma_setml = spdp_rank_with_shifts(poly, vars_, kappa, setml_shifts)

        denom_plain = comb(degree, kappa) * plain_shift_count(num_vars, ell)
        denom_setml = comb(degree, kappa) * setml_shift_count_nw(d, q, ell)

        lb_plain = (gamma_plain + denom_plain - 1) // denom_plain
        lb_setml = (gamma_setml + denom_setml - 1) // denom_setml

        print(
            f"(k={kappa},ell={ell}) "
            f"Gamma_plain={gamma_plain:>5} Gamma_setml={gamma_setml:>5} | "
            f"den_plain={denom_plain:>6} den_setml={denom_setml:>6} | "
            f"s>= plain:{lb_plain} setml:{lb_setml}"
        )


def main() -> None:
    # Small honest calibration instances.
    nw332, vars332 = nw_design_polynomial(q=3, degree=3, coeff_count=2)
    nw452, vars452 = nw_design_polynomial(q=5, degree=4, coeff_count=2)

    report_case(
        "NW_{d=3,q=3,e=2}", nw332, vars332, d=3, q=3, degree=3,
        params=[(1, 0), (1, 1), (2, 1)]
    )

    report_case(
        "NW_{d=4,q=5,e=2}", nw452, vars452, d=4, q=5, degree=4,
        params=[(1, 0), (1, 1), (2, 1)]
    )

    print("\nInterpretation")
    print("- Gamma_setml <= Gamma_plain (restricted shifts), so raw rank can drop.")
    print("- But set-multilinear denominator is much smaller, so resulting lower bound can improve.")
    print("- This is a prototype diagnostic for the LST-style direction, not a full theorem.")


if __name__ == "__main__":
    main()
