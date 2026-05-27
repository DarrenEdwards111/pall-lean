#!/usr/bin/env python3
"""
Actual NW derivative-window leading-monomial checks.

This is a finite-support calculation for the real NW polynomial

    NW_{d,q,e} = sum_{a in F_q^e} prod_{x=0}^{d-1} y_{x,a(x)}.

For a label a and derivative window D, differentiating by
prod_{x in D} y_{x,a(x)} leaves exactly the residual graph monomials of
labels b that agree with a on D.  We compute those actual derivative rows,
their leading monomials under lex order on exponent vectors, and compare them
to the residual graph pivots used in the Lean bridge.

This is a calibration script, not an asymptotic proof.
"""

from __future__ import annotations

from collections import defaultdict
from itertools import combinations, product
from typing import Iterable, Sequence


Label = tuple[int, ...]
Support = tuple[int, ...]
Exponent = tuple[int, ...]


def labels(q: int, e: int) -> list[Label]:
    return list(product(range(q), repeat=e))


def eval_code(label: Label, x: int, q: int) -> int:
    return sum(c * pow(x, power, q) for power, c in enumerate(label)) % q


def var_index(q: int, x: int, value: int) -> int:
    return x * q + value


def graph_support(q: int, d: int, label: Label, points: Iterable[int]) -> Support:
    return tuple(sorted(var_index(q, x, eval_code(label, x, q)) for x in points))


def derivative_window_row(q: int, d: int, e: int, D: tuple[int, ...], a: Label):
    row: dict[Support, int] = defaultdict(int)
    Dset = set(D)
    outside = tuple(x for x in range(d) if x not in Dset)

    for b in labels(q, e):
        if all(eval_code(a, x, q) == eval_code(b, x, q) for x in D):
            row[graph_support(q, d, b, outside)] += 1

    return dict(row)


def exponent_vector(num_vars: int, support: Support) -> Exponent:
    s = set(support)
    return tuple(1 if i in s else 0 for i in range(num_vars))


def leading_support(num_vars: int, row: dict[Support, int]) -> Support:
    nonzero = [support for support, coeff in row.items() if coeff != 0]
    if not nonzero:
        raise ValueError("zero derivative row")
    return max(nonzero, key=lambda support: exponent_vector(num_vars, support))


def monomial_exponents_le(num_vars: int, degree: int) -> list[Exponent]:
    """All exponent vectors of total degree at most degree."""
    out: list[Exponent] = []

    def rec(pos: int, remaining: int, current: list[int]) -> None:
        if pos == num_vars:
            out.append(tuple(current))
            return
        for exp in range(remaining + 1):
            current.append(exp)
            rec(pos + 1, remaining - exp, current)
            current.pop()

    rec(0, degree, [])
    return out


def add_exponents(a: Sequence[int], b: Sequence[int]) -> Exponent:
    return tuple(x + y for x, y in zip(a, b))


def shifted_row_leading_exponent(
    num_vars: int,
    row: dict[Support, int],
    shift: Exponent,
) -> Exponent:
    """Leading exponent vector of shift * row under lex order."""
    nonzero = [support for support, coeff in row.items() if coeff != 0]
    if not nonzero:
        raise ValueError("zero derivative row")
    shifted = [add_exponents(exponent_vector(num_vars, support), shift) for support in nonzero]
    return max(shifted)


def first_collisions(mapping: dict[Label, Support], limit: int = 3):
    seen: dict[Support, Label] = {}
    out = []
    for label, value in mapping.items():
        if value in seen:
            out.append((seen[value], label, value))
            if len(out) >= limit:
                return out
        else:
            seen[value] = label
    return out


def check_case(q: int, d: int, e: int, D: tuple[int, ...]) -> None:
    all_labels = labels(q, e)
    num_vars = d * q
    overlap_bound = e - 1
    outside = tuple(x for x in range(d) if x not in set(D))

    rows = {a: derivative_window_row(q, d, e, D, a) for a in all_labels}
    residuals = {a: graph_support(q, d, a, outside) for a in all_labels}
    leads = {a: leading_support(num_vars, row) for a, row in rows.items()}

    exact_indicator = {
        a: rows[a] == {residuals[a]: 1}
        for a in all_labels
    }
    lead_matches_residual = {
        a: leads[a] == residuals[a]
        for a in all_labels
    }

    distinct_residuals = len(set(residuals.values())) == len(all_labels)
    distinct_leads = len(set(leads.values())) == len(all_labels)

    print("\n" + "=" * 78)
    print(f"NW derivative-window check: d={d}, q={q}, e={e}, D={D}")
    print("=" * 78)
    print(f"labels: {len(all_labels)}")
    print(f"agreement bound: {overlap_bound}")
    print(f"|D|={len(D)} > bound? {len(D) > overlap_bound}")
    print(f"|outside|={len(outside)} > bound? {len(outside) > overlap_bound}")
    print(f"residual supports injective? {distinct_residuals}")
    print(f"leading supports injective?  {distinct_leads}")
    print(
        "actual derivative row = residual indicator rows: "
        f"{sum(exact_indicator.values())}/{len(all_labels)}"
    )
    print(
        "leading monomial equals residual graph: "
        f"{sum(lead_matches_residual.values())}/{len(all_labels)}"
    )

    if not distinct_residuals:
        print("sample residual collisions:")
        for a, b, value in first_collisions(residuals):
            print(f"  {a} and {b} -> {value}")

    if not distinct_leads:
        print("sample leading collisions:")
        for a, b, value in first_collisions(leads):
            print(f"  {a} and {b} -> {value}")

    if not all(exact_indicator.values()):
        print("first non-indicator derivative row:")
        for a in all_labels:
            if not exact_indicator[a]:
                print(f"  label {a}")
                print(f"  row terms: {len(rows[a])}")
                print(f"  residual pivot: {residuals[a]}")
                print(f"  leading support: {leads[a]}")
                break


def shifted_leading_count(q: int, d: int, e: int, kappa: int, ell: int):
    """Count distinct leading monomials of selected shifted NW partials.

    The selected family ranges over:

    * all point windows D of size kappa,
    * all labels a in F_q^e,
    * all monomial shifts of total degree at most ell.

    This is still a lower-bound diagnostic: distinct leading monomials give an
    independent subfamily, while collisions may leave additional rank that this
    count does not see.
    """
    all_labels = labels(q, e)
    num_vars = d * q
    shifts = monomial_exponents_le(num_vars, ell)

    leads: dict[tuple[tuple[int, ...], Label, Exponent], Exponent] = {}
    for D in combinations(range(d), kappa):
        for a in all_labels:
            row = derivative_window_row(q, d, e, D, a)
            for shift in shifts:
                leads[(D, a, shift)] = shifted_row_leading_exponent(num_vars, row, shift)

    return {
        "candidate_rows": len(leads),
        "distinct_leads": len(set(leads.values())),
        "collisions": len(leads) - len(set(leads.values())),
        "num_windows": len(list(combinations(range(d), kappa))),
        "num_labels": len(all_labels),
        "num_shifts": len(shifts),
    }


def check_shifted_family(
    q: int,
    d: int,
    e: int,
    kappa: int,
    ell: int,
    real_gamma: int | None = None,
) -> None:
    count = shifted_leading_count(q, d, e, kappa, ell)
    print("\n" + "=" * 78)
    print(f"NW shifted-leading count: d={d}, q={q}, e={e}, kappa={kappa}, ell={ell}")
    print("=" * 78)
    print(f"point windows: {count['num_windows']}")
    print(f"labels: {count['num_labels']}")
    print(f"shifts deg<=ell: {count['num_shifts']}")
    print(f"candidate shifted rows: {count['candidate_rows']}")
    print(f"distinct leading monomials: {count['distinct_leads']}")
    print(f"leading collisions: {count['collisions']}")
    if real_gamma is not None:
        print(f"real Gamma_{{{kappa},{ell}}}: {real_gamma}")
        print(f"count <= real Gamma? {count['distinct_leads'] <= real_gamma}")


def main() -> None:
    # d=3 cannot satisfy both |D| > e-1 and |outside| > e-1 when e=2.
    # These two checks show exactly which side fails.
    check_case(q=3, d=3, e=2, D=(0,))
    check_case(q=3, d=3, e=2, D=(0, 1))

    # d=4 has a balanced D/outside split.  This is the first small case where
    # the simple low-agreement residual-pivot bridge exactly matches real
    # derivative-window rows.
    check_case(q=5, d=4, e=2, D=(0, 1))

    # The real SPDP strength comes from using every derivative window and then
    # shifting.  These counts compare the leading-monomial model with the exact
    # ranks measured by algebraic_spdp_nw_depth3.py.
    check_shifted_family(q=5, d=4, e=2, kappa=2, ell=0, real_gamma=150)
    check_shifted_family(q=5, d=4, e=2, kappa=2, ell=1, real_gamma=1550)


if __name__ == "__main__":
    main()
