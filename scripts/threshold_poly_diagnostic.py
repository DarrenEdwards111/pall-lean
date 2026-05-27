#!/usr/bin/env python3
"""
Exact multilinear polynomial diagnostics for small threshold circuits.

For f:{0,1}^n->{0,1}, the unique multilinear representation is
  f(x)= sum_S a_S prod_{i in S} x_i
with Mobius coefficients a_S = sum_{T subset S} (-1)^{|S|-|T|} f(1_T).

We report degree and monomial sparsity. Dense/high-degree at small n means the
exact polynomial representation is hardness-certificate shaped, not immediate
Williams-style algorithm fuel.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
import random


def popcount(x: int) -> int:
    return x.bit_count()


def mobius_coeffs(values):
    """In-place zeta inverse on subset lattice. values[mask]=f(mask)."""
    a = [int(v) for v in values]
    n = (len(a)).bit_length() - 1
    for i in range(n):
        bit = 1 << i
        for mask in range(1 << n):
            if mask & bit:
                a[mask] -= a[mask ^ bit]
    return a


def stats_for_truth(n, f):
    vals = [f(mask) for mask in range(1 << n)]
    coeffs = mobius_coeffs(vals)
    supp = [m for m, c in enumerate(coeffs) if c != 0]
    deg = max((popcount(m) for m in supp), default=0)
    sparsity = len(supp)
    max_abs = max((abs(coeffs[m]) for m in supp), default=0)
    full = 1 << n
    top = sum(1 for m in supp if popcount(m) == deg)
    return {"degree": deg, "sparsity": sparsity, "density": sparsity / full, "top_degree_terms": top, "max_abs_coeff": max_abs}


def bits(mask, n):
    return [(mask >> i) & 1 for i in range(n)]


def ltf(weights, theta):
    n = len(weights)
    return lambda mask: int(sum(weights[i] * ((mask >> i) & 1) for i in range(n)) >= theta)


def majority(n):
    return ltf([1] * n, (n + 1) // 2)


def exact_k(n, k):
    return lambda mask: int(popcount(mask) == k)


def threshold_of_ands(n, block=2, top_theta=None):
    # Bottom gates are pairwise ANDs over disjoint blocks; top threshold counts satisfied blocks.
    groups = [list(range(i, min(i + block, n))) for i in range(0, n, block)]
    if top_theta is None:
        top_theta = (len(groups) + 1) // 2
    def f(mask):
        count = 0
        for g in groups:
            count += int(all((mask >> i) & 1 for i in g))
        return int(count >= top_theta)
    return f


def threshold_of_majorities(n, block=3, top_theta=None):
    groups = [list(range(i, min(i + block, n))) for i in range(0, n, block)]
    if top_theta is None:
        top_theta = (len(groups) + 1) // 2
    def f(mask):
        count = 0
        for g in groups:
            ones = sum((mask >> i) & 1 for i in g)
            count += int(ones >= (len(g) + 1) // 2)
        return int(count >= top_theta)
    return f


def random_ltf_of_ltfs(n, m=None, seed=0, weight_range=(-2, 2)):
    rng = random.Random(seed)
    if m is None:
        m = n
    bottom = []
    for _ in range(m):
        weights = [rng.randint(*weight_range) for _ in range(n)]
        # avoid all-zero gate
        if all(w == 0 for w in weights):
            weights[rng.randrange(n)] = 1
        # threshold around half possible positive mass; random-ish
        vals = [sum(weights[i] * ((mask >> i) & 1) for i in range(n)) for mask in range(1 << min(n, 10))]
        theta = sorted(vals)[len(vals)//2]
        bottom.append((weights, theta))
    top_weights = [rng.choice([-2, -1, 1, 2]) for _ in range(m)]
    # threshold around median bottom score sampled over all masks if small
    scores = []
    for mask in range(1 << n):
        ys = [int(sum(w[i] * ((mask >> i) & 1) for i in range(n)) >= th) for w, th in bottom]
        scores.append(sum(top_weights[j] * ys[j] for j in range(m)))
    top_theta = sorted(scores)[len(scores)//2]
    def f(mask):
        ys = [int(sum(w[i] * ((mask >> i) & 1) for i in range(n)) >= th) for w, th in bottom]
        return int(sum(top_weights[j] * ys[j] for j in range(m)) >= top_theta)
    return f


def run():
    families = [
        ("MAJ_n", lambda n: majority(n)),
        ("EXACT_half", lambda n: exact_k(n, n // 2)),
        ("THR_of_pair_AND", lambda n: threshold_of_ands(n, block=2)),
        ("THR_of_block_MAJ3", lambda n: threshold_of_majorities(n, block=3)),
        ("random_LTF_of_LTF_seed1", lambda n: random_ltf_of_ltfs(n, m=n, seed=1)),
    ]
    print("family,n,degree,sparsity,total_monomials,density,top_degree_terms,max_abs_coeff")
    for n in range(4, 13):
        for name, maker in families:
            st = stats_for_truth(n, maker(n))
            print(f"{name},{n},{st['degree']},{st['sparsity']},{1<<n},{st['density']:.4f},{st['top_degree_terms']},{st['max_abs_coeff']}")

if __name__ == "__main__":
    run()
