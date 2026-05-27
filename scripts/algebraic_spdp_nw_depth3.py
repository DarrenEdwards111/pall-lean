#!/usr/bin/env python3
"""
Small exact SPDP calibration for the algebraic-circuit pivot.

This script is deliberately not an asymptotic proof.  It checks the finite
instrument on small permanent/determinant/Nisan-Wigderson instances and then
prints the rigorous homogeneous depth-3 denominator

    choose(degree, kappa) * M(num_vars, ell),

where M(N, ell) is the number of monomials of total degree <= ell.

The theorem layer lives in
PallLean/Paper93/DeepMath/AlgebraicSPDP/ArithmeticCircuitSPDPPivot.lean:
an analytic NW support-independence lower bound plus this denominator gives
a depth-3 product-gate lower bound.
"""

from __future__ import annotations

from itertools import combinations, product
from math import comb
from typing import Iterable, Sequence

from sympy import Matrix, Poly, Symbol, diff, expand, symbols


def monomial_exponents_le(num_vars: int, degree: int) -> list[tuple[int, ...]]:
    """All exponent vectors of total degree at most degree."""
    out: list[tuple[int, ...]] = []

    def rec(pos: int, remaining: int, current: list[int]) -> None:
        if pos == num_vars:
            out.append(tuple(current))
            return
        for e in range(remaining + 1):
            current.append(e)
            rec(pos + 1, remaining - e, current)
            current.pop()

    rec(0, degree, [])
    return out


def monomial(vars_: Sequence[Symbol], exp: Sequence[int]):
    term = 1
    for x, e in zip(vars_, exp):
        if e:
            term *= x**e
    return term


def spdp_rank(poly, vars_: Sequence[Symbol], kappa: int, ell: int) -> int:
    """Exact shifted-partial-derivative rank over QQ using Sympy matrices."""
    rows = []
    shifts = [monomial(vars_, e) for e in monomial_exponents_le(len(vars_), ell)]

    for deriv_vars in combinations(vars_, kappa):
        p = poly
        for x in deriv_vars:
            p = diff(p, x)
            if p == 0:
                break
        if p == 0:
            continue
        for shift in shifts:
            rows.append(expand(shift * p))

    if not rows:
        return 0

    monoms = set()
    row_dicts = []
    for row in rows:
        coeffs = Poly(row, *vars_, domain="QQ").as_dict()
        row_dicts.append(coeffs)
        monoms.update(coeffs)

    basis = sorted(monoms)
    matrix_rows = [[coeffs.get(m, 0) for m in basis] for coeffs in row_dicts]
    return int(Matrix(matrix_rows).rank())


def permanent_matrix_poly(n: int, sign: bool = False):
    vars_ = symbols(f"x0:{n*n}")

    def x(i: int, j: int):
        return vars_[i * n + j]

    total = 0
    for perm in permutations(range(n)):
        term = 1
        inv = 0
        for i, j in enumerate(perm):
            term *= x(i, j)
            for ii in range(i):
                if perm[ii] > j:
                    inv += 1
        total += (-1 if sign and inv % 2 else 1) * term
    return expand(total), vars_


def permutations(items: Iterable[int]):
    items = list(items)
    if not items:
        yield ()
        return
    for i, item in enumerate(items):
        rest = items[:i] + items[i + 1 :]
        for p in permutations(rest):
            yield (item,) + p


def nw_design_polynomial(q: int, degree: int, coeff_count: int):
    """NW_{degree,q,coeff_count}: sum_a prod_i x_{i,p_a(i)} over F_q.

    This small calibration uses prime q and univariate polynomials over F_q
    with coeff_count coefficients, i.e. degree < coeff_count.  It requires
    degree <= q so the evaluation points 0,...,degree-1 are distinct in F_q.
    """
    if degree > q:
        raise ValueError("this small prime-field model requires degree <= q")

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


def depth3_denominator(num_vars: int, degree: int, kappa: int, ell: int) -> int:
    return comb(degree, kappa) * comb(num_vars + ell, ell)


def report(name: str, poly, vars_: Sequence[Symbol], degree: int, params):
    print(f"\n{name}")
    print("-" * len(name))
    for kappa, ell in params:
        gamma = spdp_rank(poly, vars_, kappa, ell)
        denom = depth3_denominator(len(vars_), degree, kappa, ell)
        lower = (gamma + denom - 1) // denom if denom else 0
        print(
            f"(kappa={kappa}, ell={ell}) "
            f"Gamma={gamma:>4}  denom={denom:>4}  depth3 s >= {lower}"
        )


def main() -> None:
    params = [(1, 0), (1, 1), (2, 1)]

    perm3, matrix_vars = permanent_matrix_poly(3, sign=False)
    det3, _ = permanent_matrix_poly(3, sign=True)
    nw332, nw_vars = nw_design_polynomial(q=3, degree=3, coeff_count=2)
    nw452, nw4_vars = nw_design_polynomial(q=5, degree=4, coeff_count=2)

    print("=" * 78)
    print("Algebraic SPDP calibration: permanent, determinant, NW design")
    print("=" * 78)
    report("perm_3", perm3, matrix_vars, degree=3, params=params)
    report("det_3", det3, matrix_vars, degree=3, params=params)
    report("NW_{d=3,q=3,e=2}", nw332, nw_vars, degree=3, params=params)
    report("NW_{d=4,q=5,e=2}", nw452, nw4_vars, degree=4, params=[(1, 0), (1, 1)])

    print("\nClosed form check at ell=0 for perm_3")
    for kappa in (1, 2):
        gamma = spdp_rank(perm3, matrix_vars, kappa, 0)
        expected = comb(3, kappa) ** 2
        print(f"kappa={kappa}: Gamma={gamma}, choose(3,{kappa})^2={expected}")

    print("\nInterpretation")
    print("The exact ranks are calibration.  The asymptotic lower bound must")
    print("come from a support-independence theorem for the NW design; the")
    print("Lean file proves the conversion from that theorem to a depth-3")
    print("product-gate lower bound.")


if __name__ == "__main__":
    main()
