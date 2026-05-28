#!/usr/bin/env python3
"""
Scaling EA for SPDP lower-bound FAMILIES (the real version).

Single-scale raw rank is meaningless (it just creeps to the ceiling).  The
honest target is the LOWER-BOUND RATIO and its GROWTH across scales:

    R(family @ scale) = Gamma_{k,l}(family) / Gamma_{k,l}(single set-ml product)

R is a genuine lower bound on the number of products needed by a set-multilinear
depth-3 (Sum-Prod-Sum) circuit.  A family is BETTER than NW iff its R is larger
AND grows faster as the scale grows.

Scale-free family encoding (set-ml selections = codewords over Z_q):
  genome = (exps, sign_bits)
    exps      : a set of generator exponents, |exps| = k
    sign_bits : exp -> {0,1}, giving a scale-free sign rule
  At scale (d, q): for every coefficient vector c in (Z_q)^k, the selection is
    f(i) = sum_t c[t] * i^{exps[t]}  (mod q),  i in [d]
  with sign (-1)^{ sum_t sign_bits[t]*c[t]  mod 2 }.
  NW_{d,q,e} = exps {0,1,...,e-1}, all signs + (Reed-Solomon / MDS code).

We evolve at q=5 (cheap), then compare finalists vs NW across q in {5,7}.
Exact rank over F_p via vectorised Gaussian elimination.
"""

import numpy as np
import random
import itertools
from itertools import combinations_with_replacement, combinations

P = 32749


def rank_mod_p(M):
    M = (M.astype(np.int64)) % P
    nrows, ncols = M.shape
    pr = rank = 0
    for c in range(ncols):
        nz = np.nonzero(M[pr:, c])[0]
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


def diff_poly(poly, v):
    out = {}
    for exps, c in poly.items():
        e = exps[v]
        if e == 0:
            continue
        new = list(exps); new[v] = e - 1
        key = tuple(new)
        out[key] = out.get(key, 0) + c * e
    return {k: val for k, val in out.items() if val % P != 0}


def mul_monomial(poly, shift_exps):
    out = {}
    for exps, c in poly.items():
        new = tuple(a + b for a, b in zip(exps, shift_exps))
        out[new] = out.get(new, 0) + c
    return out


def mul_polys(p1, p2):
    out = {}
    for e1, c1 in p1.items():
        for e2, c2 in p2.items():
            k = tuple(a + b for a, b in zip(e1, e2))
            out[k] = (out.get(k, 0) + c1 * c2) % P
    return {k: v for k, v in out.items() if v % P != 0}


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
    rows, colidx = [], {}
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


def selection_to_exps(f, q, n):
    e = [0] * n
    for i, j in enumerate(f):
        e[i * q + j] = 1
    return tuple(e)


_g1_cache = {}
def g1(d, q, kappa, ell):
    key = (d, q, kappa, ell)
    if key in _g1_cache:
        return _g1_cache[key]
    n = d * q
    best = 0
    for seed in (1, 2):
        rng = random.Random(seed)
        poly = {tuple([0] * n): 1}
        for i in range(d):
            lin = {}
            for j in range(q):
                e = [0] * n; e[i * q + j] = 1
                lin[tuple(e)] = rng.randrange(1, P)
            poly = mul_polys(poly, lin)
        best = max(best, spdp_rank(poly, n, kappa, ell))
    _g1_cache[key] = best
    return best


def gen_family(exps, sign_bits, d, q):
    n = d * q
    k = len(exps)
    poly = {}
    for c in itertools.product(range(q), repeat=k):
        f = tuple(sum(c[t] * pow(i, exps[t], q) for t in range(k)) % q
                  for i in range(d))
        key = selection_to_exps(f, q, n)
        sgn = -1 if (sum(sign_bits[t] * c[t] for t in range(k)) % 2) else 1
        poly[key] = poly.get(key, 0) + sgn
    return {k2: v for k2, v in poly.items() if v % P != 0}


def ratio(exps, sign_bits, d, q, kappa, ell):
    n = d * q
    g = g1(d, q, kappa, ell)
    if g == 0:
        return 0.0, 0
    poly = gen_family(exps, sign_bits, d, q)
    r = spdp_rank(poly, n, kappa, ell)
    return r / g, len(poly)


# ---------- evolutionary search at the cheap scale ----------
def evolve(d, q_train, kappa, ell, maxdeg=4, k=2, gens=20, pop=20, seed=0):
    random.seed(seed)
    all_exps = list(combinations(range(maxdeg + 1), k))
    sign_space = list(itertools.product((0, 1), repeat=k))

    def fitness(g):
        return ratio(g[0], g[1], d, q_train, kappa, ell)[0]

    # seed: every exponent set with all-plus signs (covers NW and all RS-like)
    population = [(e, (0,) * k) for e in all_exps]
    while len(population) < pop:
        e = random.choice(all_exps)
        s = random.choice(sign_space)
        population.append((e, s))

    cache = {}
    def fit(g):
        if g not in cache:
            cache[g] = fitness(g)
        return cache[g]

    for _ in range(gens):
        population = sorted(set(population), key=fit, reverse=True)
        survivors = population[: max(3, pop // 3)]
        children = []
        while len(survivors) + len(children) < pop:
            pe, ps = random.choice(survivors)
            if random.random() < 0.5:           # mutate exponents
                pe = random.choice(all_exps)
            else:                                # mutate sign rule
                i = random.randrange(k)
                ps = tuple(b ^ (1 if j == i else 0) for j, b in enumerate(ps))
            children.append((pe, ps))
        population = survivors + children

    ranked = sorted(set(population), key=fit, reverse=True)
    return ranked


if __name__ == "__main__":
    d, kappa, ell, k = 3, 1, 1, 2
    NW = (tuple(range(k)), (0,) * k)        # exps {0,1}, all + : Reed-Solomon

    print(f"set-ml degree d={d}, generator size k={k}, window (k,l)=({kappa},{ell})")
    print("NW = Reed-Solomon family exps", NW[0], "signs", NW[1])

    ranked = evolve(d, 5, kappa, ell, k=k, gens=20, pop=20, seed=7)

    # finalists: NW + top distinct non-NW candidates
    finalists = [NW]
    for g in ranked:
        if g != NW and g not in finalists:
            finalists.append(g)
        if len(finalists) >= 4:
            break

    scales = [5, 7]
    print(f"\n{'family (exps/signs)':>26} | " +
          " | ".join(f"R(q={q})" for q in scales) + " |  growth R7/R5 | #mons")
    print("-" * 80)
    rows = []
    for g in finalists:
        Rs, mons = [], 0
        for q in scales:
            r, m = ratio(g[0], g[1], d, q, kappa, ell)
            Rs.append(r); mons = m
        growth = Rs[1] / Rs[0] if Rs[0] else float('nan')
        tag = "NW" if g == NW else "  "
        label = f"{tag} {g[0]} s{g[1]}"
        print(f"{label:>26} | " +
              " | ".join(f"{r:6.3f}" for r in Rs) +
              f" |   {growth:6.4f}     | {mons}")
        rows.append((g, Rs, growth))

    nw_R = rows[0][1]
    nw_growth = rows[0][2]
    print("\nVerdict (vs NW, at q=7 and in growth):")
    beat = False
    for g, Rs, growth in rows[1:]:
        better_bound = Rs[-1] > nw_R[-1] + 1e-9
        faster = growth > nw_growth + 1e-9
        if better_bound and faster:
            print(f"  {g[0]} s{g[1]}: STRICTLY beats NW (higher R AND faster growth)")
            beat = True
        elif better_bound:
            print(f"  {g[0]} s{g[1]}: higher R at q=7 but not faster growth")
        elif faster:
            print(f"  {g[0]} s{g[1]}: faster growth but lower R at q=7")
    if not beat:
        print("  No family strictly beats Reed-Solomon/NW (higher R AND faster growth).")
