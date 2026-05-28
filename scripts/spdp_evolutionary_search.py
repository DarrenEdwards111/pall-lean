#!/usr/bin/env python3
"""
Evolutionary search for better restricted-model SPDP lower-bound candidates.

HONEST SCOPE.  This does NOT attempt P vs NP.  It treats SPDP rank as a
restricted-model lower-bound MEASURE and asks a falsifiable question:

    Among set-multilinear polynomials with at most as many monomials as the
    Nisan-Wigderson design NW_{d,q,e}, can an evolutionary algorithm find one
    with STRICTLY higher exact Gamma_{kappa,ell} than NW itself?

NW is the celebrated incumbent (its design property -> near-maximal shifted
partial rank).  If NW is near-optimal, the EA will tie or barely beat it --
that is itself a real result ("NW is hard to beat at these params").  If the
EA beats it by a margin, that is a concrete candidate worth examining.

Variables: n = d*q, indexed (bucket i in [d], value j in [q]) -> i*q+j.
A set-multilinear monomial is a selection f:[d]->[q], giving prod_i x_{i,f(i)}.
A candidate polynomial is a signed set of such selections.

Exact rank is computed over F_p with a vectorised (numpy) Gaussian elimination
(= rank over Q for all but finitely many primes).
"""

import numpy as np
import random
import itertools
from itertools import combinations_with_replacement

P = 32749  # prime; (P-1)^2 < 2^31, safe for int64 elimination


# ---------- exact rank over F_p (vectorised) ----------
def rank_mod_p(M):
    M = (M.astype(np.int64)) % P
    nrows, ncols = M.shape
    pr = 0
    rank = 0
    for c in range(ncols):
        col = M[pr:, c] % P
        nz = np.nonzero(col)[0]
        if nz.size == 0:
            continue
        piv = pr + int(nz[0])
        if piv != pr:
            M[[pr, piv]] = M[[piv, pr]]
        inv = pow(int(M[pr, c]), P - 2, P)
        M[pr] = (M[pr] * inv) % P
        factors = M[:, c].copy()
        factors[pr] = 0
        if factors.any():
            M = (M - np.outer(factors, M[pr])) % P
        pr += 1
        rank += 1
        if pr == nrows:
            break
    return rank


# ---------- monomial (exponent-tuple) algebra ----------
def diff_poly(poly, v):
    out = {}
    for exps, c in poly.items():
        e = exps[v]
        if e == 0:
            continue
        new = list(exps)
        new[v] = e - 1
        key = tuple(new)
        out[key] = (out.get(key, 0) + c * e)
    return {k: val for k, val in out.items() if val % P != 0}


def mul_monomial(poly, shift_exps):
    out = {}
    for exps, c in poly.items():
        new = tuple(a + b for a, b in zip(exps, shift_exps))
        out[new] = out.get(new, 0) + c
    return out


def shifts_up_to(n, ell):
    res = []
    for d in range(ell + 1):
        for combo in combinations_with_replacement(range(n), d):
            e = [0] * n
            for v in combo:
                e[v] += 1
            res.append(tuple(e))
    return res


def spdp_rank(poly, n, kappa, ell):
    """Gamma_{kappa,ell}(poly) = dim < x^{<=ell} . d^{=kappa} poly >."""
    partials = []
    for combo in combinations_with_replacement(range(n), kappa):
        d = poly
        for v in combo:
            d = diff_poly(d, v)
            if not d:
                break
        if d:
            partials.append(d)
    if not partials:
        return 0
    shifts = shifts_up_to(n, ell)
    rows = []
    colidx = {}
    for pd in partials:
        for s in shifts:
            prod = mul_monomial(pd, s)
            rows.append(prod)
            for m in prod:
                if m not in colidx:
                    colidx[m] = len(colidx)
    M = np.zeros((len(rows), len(colidx)), dtype=np.int64)
    for r, prod in enumerate(rows):
        for m, c in prod.items():
            M[r, colidx[m]] = c % P
    return rank_mod_p(M)


# ---------- selections <-> polynomial ----------
def selection_to_exps(f, q, n):
    e = [0] * n
    for i, j in enumerate(f):
        e[i * q + j] = 1
    return tuple(e)


def genome_to_poly(genome, q, n):
    poly = {}
    for f, sign in genome.items():
        poly[selection_to_exps(f, q, n)] = sign
    return poly


# ---------- Nisan-Wigderson design (incumbent baseline) ----------
def nw_design(d, q, e):
    """NW_{d,q,e}: for each univariate poly of degree < e over Z_q, the
    selection f(i) = poly evaluated at field element i (mod q), i in [d].
    Requires d <= q and q prime (we use q prime).  q^e monomials, each pair
    sharing < e variables."""
    genome = {}
    for coeffs in itertools.product(range(q), repeat=e):
        f = tuple(
            sum(coeffs[k] * pow(i, k, q) for k in range(e)) % q
            for i in range(d)
        )
        genome[f] = 1
    return genome


# ---------- evolutionary algorithm ----------
def random_selection(d, q):
    return tuple(random.randrange(q) for _ in range(d))


def mutate(genome, d, q, budget):
    g = dict(genome)
    op = random.random()
    if op < 0.35 and len(g) < budget:                       # add
        f = random_selection(d, q)
        g[f] = random.choice([-1, 1])
    elif op < 0.55 and len(g) > 2:                          # remove
        del g[random.choice(list(g.keys()))]
    elif op < 0.80:                                         # flip sign
        k = random.choice(list(g.keys()))
        g[k] = -g[k]
    else:                                                   # swap
        if len(g) > 1:
            del g[random.choice(list(g.keys()))]
        if len(g) < budget:
            g[random_selection(d, q)] = random.choice([-1, 1])
    return g


def evolve(d, q, e, kappa, ell, pop=24, gens=30, seed=0):
    random.seed(seed)
    n = d * q
    budget = q ** e

    nw = nw_design(d, q, e)
    nw_poly = genome_to_poly(nw, q, n)
    nw_rank = spdp_rank(nw_poly, n, kappa, ell)

    cache = {}

    def fitness(g):
        key = frozenset(g.items())
        if key in cache:
            return cache[key]
        r = spdp_rank(genome_to_poly(g, q, n), n, kappa, ell)
        cache[key] = r
        return r

    # population: NW seed + random individuals
    population = [dict(nw)]
    while len(population) < pop:
        size = random.randint(budget // 2, budget)
        g = {}
        while len(g) < size:
            g[random_selection(d, q)] = random.choice([-1, 1])
        population.append(g)

    best, best_fit = dict(nw), nw_rank
    history = []
    for gen in range(gens):
        scored = sorted(population, key=fitness, reverse=True)
        if fitness(scored[0]) > best_fit:
            best, best_fit = dict(scored[0]), fitness(scored[0])
        history.append(best_fit)
        survivors = scored[: max(2, pop // 3)]
        children = []
        while len(survivors) + len(children) < pop:
            parent = random.choice(survivors)
            children.append(mutate(parent, d, q, budget))
        population = survivors + children

    return {
        "n": n, "budget": budget, "kappa": kappa, "ell": ell,
        "nw_rank": nw_rank, "best_rank": best_fit,
        "best_mons": len(best), "history": history, "best": best,
    }


if __name__ == "__main__":
    # set-multilinear regime: degree d=3, field size q=5, NW degree e=2
    # -> 15 variables, 25-monomial budget, degree-3 polynomials
    for (kappa, ell) in [(1, 1), (2, 1)]:
        res = evolve(d=3, q=5, e=2, kappa=kappa, ell=ell, pop=24, gens=30, seed=1)
        print(f"\n=== set-ml d=3 q=5 e=2 | window (kappa,ell)=({kappa},{ell}) ===")
        print(f"  variables           : {res['n']}")
        print(f"  monomial budget     : {res['budget']}  (= NW count)")
        print(f"  NW design rank      : {res['nw_rank']}")
        print(f"  best EA-found rank  : {res['best_rank']}  ({res['best_mons']} monomials)")
        delta = res['best_rank'] - res['nw_rank']
        verdict = ("EA BEAT NW" if delta > 0 else
                   "EA tied NW" if delta == 0 else "EA below NW")
        print(f"  delta vs NW         : {delta:+d}   -> {verdict}")
        print(f"  best-so-far history : {res['history'][::5]}")
