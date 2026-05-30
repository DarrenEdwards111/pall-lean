#!/usr/bin/env python3
"""
Evolutionary search for small structured SPDP-rank candidates.

This is an experiment, not a theorem.  It searches set-multilinear polynomial
supports

    f(x) = sum_{w in S} c_w prod_i x_{i,w_i}

where each word w chooses one variable from each bucket.  The fitness is the
exact shifted-partial derivative rank Gamma_{k,ell}(f), normalized by the
standard homogeneous depth-3 denominator choose(d,k) * M(N,ell).

The point is to test whether local search can find a stronger SPDP signal than
the NW design at the same tiny parameters.  High rank by itself is not a P-vs-NP
proof; the output is useful only as evidence for restricted algebraic lower
bound targets.
"""

from __future__ import annotations

import argparse
import itertools
import math
import random
from dataclasses import dataclass


PRIME = 2_147_483_647


Word = tuple[int, ...]
Candidate = tuple[tuple[Word, int], ...]
Monomial = tuple[int, ...]


def compositions(total: int, parts: int):
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest


def shift_exponents(num_vars: int, ell: int) -> list[Monomial]:
    out: list[Monomial] = []
    for degree in range(ell + 1):
        out.extend(compositions(degree, num_vars))
    return out


def word_vars(q: int, word: Word) -> tuple[int, ...]:
    return tuple(i * q + value for i, value in enumerate(word))


def add_shift(base_vars: tuple[int, ...], shift: Monomial, num_vars: int) -> Monomial:
    exps = [0] * num_vars
    for v in base_vars:
        exps[v] += 1
    for i, e in enumerate(shift):
        exps[i] += e
    return tuple(exps)


def sparse_rank(rows: list[dict[Monomial, int]], p: int = PRIME) -> int:
    """Sparse Gaussian elimination over F_p, pivoting by lexicographic key."""
    basis: dict[Monomial, dict[Monomial, int]] = {}
    for row0 in rows:
        row = {k: v % p for k, v in row0.items() if v % p}
        while row:
            pivot = max(row)
            coeff = row[pivot] % p
            if pivot not in basis:
                inv = pow(coeff, p - 2, p)
                basis[pivot] = {k: (v * inv) % p for k, v in row.items() if (v * inv) % p}
                break
            prow = basis[pivot]
            for k, v in prow.items():
                new = (row.get(k, 0) - coeff * v) % p
                if new:
                    row[k] = new
                elif k in row:
                    del row[k]
    return len(basis)


def spdp_rank_setml(candidate: Candidate, d: int, q: int, kappa: int, ell: int) -> int:
    num_vars = d * q
    shifts = shift_exponents(num_vars, ell)
    term_data = [
        (set(word_vars(q, word)), word_vars(q, word), coeff)
        for word, coeff in candidate
    ]

    rows: list[dict[Monomial, int]] = []
    for deriv in itertools.combinations(range(num_vars), kappa):
        deriv_set = set(deriv)
        for shift in shifts:
            row: dict[Monomial, int] = {}
            for var_set, vars_tuple, coeff in term_data:
                if not deriv_set.issubset(var_set):
                    continue
                residual = tuple(v for v in vars_tuple if v not in deriv_set)
                mono = add_shift(residual, shift, num_vars)
                row[mono] = (row.get(mono, 0) + coeff) % PRIME
            if row:
                rows.append(row)
    return sparse_rank(rows)


def depth3_denominator(d: int, q: int, kappa: int, ell: int) -> int:
    num_vars = d * q
    return math.comb(d, kappa) * math.comb(num_vars + ell, ell)


def nw_candidate(d: int, q: int, e: int) -> Candidate:
    terms: list[tuple[Word, int]] = []
    for coeffs in itertools.product(range(q), repeat=e):
        word = tuple(
            sum(c * pow(x, power, q) for power, c in enumerate(coeffs)) % q
            for x in range(d)
        )
        terms.append((word, 1))
    return canonicalize(terms)


def random_candidate(d: int, q: int, term_count: int, rng: random.Random) -> Candidate:
    universe = list(itertools.product(range(q), repeat=d))
    words = rng.sample(universe, term_count)
    return canonicalize((word, rng.choice([-1, 1])) for word in words)


def canonicalize(items) -> Candidate:
    coeffs: dict[Word, int] = {}
    for word, coeff in items:
        coeffs[word] = coeffs.get(word, 0) + coeff
    cleaned = []
    for word, coeff in coeffs.items():
        c = coeff % PRIME
        if c == 0:
            continue
        sign = -1 if c == PRIME - 1 else 1
        cleaned.append((word, sign))
    return tuple(sorted(cleaned))


def mutate(candidate: Candidate, d: int, q: int, term_count: int, rng: random.Random) -> Candidate:
    coeffs = {word: coeff for word, coeff in candidate}
    universe_size = q ** d

    for _ in range(rng.randint(1, 3)):
        op = rng.choice(["replace", "flip"])
        if op == "flip" and coeffs:
            word = rng.choice(list(coeffs))
            coeffs[word] *= -1
        else:
            if coeffs:
                del coeffs[rng.choice(list(coeffs))]
            while len(coeffs) < min(term_count, universe_size):
                word = tuple(rng.randrange(q) for _ in range(d))
                if word not in coeffs:
                    coeffs[word] = rng.choice([-1, 1])
                    break

    while len(coeffs) < min(term_count, universe_size):
        word = tuple(rng.randrange(q) for _ in range(d))
        coeffs.setdefault(word, rng.choice([-1, 1]))

    return canonicalize(coeffs.items())


@dataclass(frozen=True)
class Scored:
    gamma: int
    lower_bound: int
    ratio: float
    candidate: Candidate
    label: str


def score_candidate(
    candidate: Candidate,
    label: str,
    d: int,
    q: int,
    kappa: int,
    ell: int,
    cache: dict[Candidate, Scored],
) -> Scored:
    if candidate in cache:
        cached = cache[candidate]
        return Scored(cached.gamma, cached.lower_bound, cached.ratio, candidate, label)
    gamma = spdp_rank_setml(candidate, d, q, kappa, ell)
    denom = depth3_denominator(d, q, kappa, ell)
    lower = (gamma + denom - 1) // denom
    scored = Scored(gamma, lower, gamma / denom, candidate, label)
    cache[candidate] = scored
    return scored


def summarize_candidate(candidate: Candidate, limit: int = 8) -> str:
    head = ", ".join(f"{c:+d}{w}" for w, c in candidate[:limit])
    if len(candidate) > limit:
        head += f", ... ({len(candidate)} terms)"
    return head


def run(args) -> None:
    rng = random.Random(args.seed)
    cache: dict[Candidate, Scored] = {}

    baseline = nw_candidate(args.d, args.q, args.e)
    population: list[Candidate] = [] if args.no_baseline else [baseline]
    while len(population) < args.population:
        population.append(random_candidate(args.d, args.q, args.terms, rng))

    nw_reference = score_candidate(
        baseline, "NW baseline", args.d, args.q, args.kappa, args.ell, cache
    )
    best: Scored | None = None
    print("=" * 88)
    print("Evolutionary SPDP candidate search")
    print("=" * 88)
    print(
        f"d={args.d}, q={args.q}, terms={args.terms}, kappa={args.kappa}, ell={args.ell}, "
        f"population={args.population}, generations={args.generations}, seed={args.seed}"
    )
    print(
        f"depth-3 denominator = {depth3_denominator(args.d, args.q, args.kappa, args.ell)}"
    )
    print(
        f"baseline NW: Gamma={nw_reference.gamma}, "
        f"s>={nw_reference.lower_bound}, ratio={nw_reference.ratio:.3f}"
    )
    if args.no_baseline:
        print("population mode: random-only search; NW is reported only as a reference")

    for gen in range(args.generations + 1):
        scored = [
            score_candidate(c, f"gen{gen}", args.d, args.q, args.kappa, args.ell, cache)
            for c in population
        ]
        scored.sort(key=lambda s: (s.gamma, s.lower_bound), reverse=True)
        if best is None or scored[0].gamma > best.gamma:
            best = scored[0]
        print(
            f"gen {gen:02d}: best Gamma={scored[0].gamma:>5}, "
            f"s>={scored[0].lower_bound:>3}, ratio={scored[0].ratio:.3f}, "
            f"global best={best.gamma}"
        )

        elites = [s.candidate for s in scored[: max(2, args.population // 4)]]
        next_pop = list(elites)
        while len(next_pop) < args.population:
            parent = rng.choice(elites)
            next_pop.append(mutate(parent, args.d, args.q, args.terms, rng))
        population = next_pop

    print("\nBest candidate")
    print("-" * 88)
    assert best is not None
    print(f"Gamma={best.gamma}")
    print(f"depth-3 lower bound s >= {best.lower_bound}")
    print(f"ratio Gamma/denom = {best.ratio:.3f}")
    print(summarize_candidate(best.candidate))
    print("\nInterpretation")
    print("- If the search only matches NW, NW is already locally rank-maximal at these parameters.")
    print("- If it beats NW, the candidate is worth analyzing as a restricted algebraic lower-bound object.")
    print("- Either outcome is about restricted algebraic SPDP strength, not full P vs NP.")


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--d", type=int, default=4)
    parser.add_argument("--q", type=int, default=5)
    parser.add_argument("--e", type=int, default=2)
    parser.add_argument("--terms", type=int, default=25)
    parser.add_argument("--kappa", type=int, default=2)
    parser.add_argument("--ell", type=int, default=1)
    parser.add_argument("--population", type=int, default=10)
    parser.add_argument("--generations", type=int, default=6)
    parser.add_argument("--seed", type=int, default=1729)
    parser.add_argument("--no-baseline", action="store_true")
    return parser.parse_args()


if __name__ == "__main__":
    run(parse_args())
