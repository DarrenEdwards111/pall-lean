#!/usr/bin/env python3
"""
Can an evolutionary algorithm 'produce P vs NP'?

A lower-bound proof by a measure mu needs:  mu small on EVERY easy function,
mu large on the hard target.  So we make that searchable: let an EA evolve an
efficiently-computable measure mu (a weighting over standard Fourier/complexity
features of a Boolean function's truth table) and reward it for separating

    EASY      : functions built by small random circuits (small-circuit, in P)
    RANDOM    : uniform random truth tables (generic / 'hard-looking')

Then we run the honest tests the search itself cannot optimise:

  (1) does it generalise to held-out easy/random?  (sanity)
  (2) LARGENESS: what fraction of ALL functions does mu flag 'hard'?
      -> if large, mu is a 'natural property' (Razborov-Rudich constructive+large)
  (3) the decisive one -- SCRAMBLE: functions built by small XOR-heavy circuits
      (still small-circuit = EASY) but engineered to look random.
      A genuine P-vs-NP measure MUST keep these LOW (they are in P).
      A natural property will mark them HARD.

n is small (truth tables must be enumerable), so this cannot *prove* anything;
it demonstrates the *mechanism* of what EA search produces here.
"""

import numpy as np
import random

n = 6
N = 1 << n            # 64 truth-table entries
FULL = (1 << N) - 1


# ---------- truth-table primitives ----------
def var_tt(i):
    v = 0
    for a in range(N):
        if (a >> i) & 1:
            v |= (1 << a)
    return v

INPUTS = [var_tt(i) for i in range(n)]


def random_circuit_tt(num_gates, xor_heavy=False):
    pool = list(INPUTS)
    for _ in range(num_gates):
        op = random.random()
        a = random.choice(pool)
        if op < (0.7 if xor_heavy else 0.34):
            b = random.choice(pool); r = (a ^ b) & FULL
        elif op < (0.85 if xor_heavy else 0.67):
            b = random.choice(pool); r = (a & b) & FULL
        else:
            b = random.choice(pool); r = (a | b) & FULL
        if random.random() < 0.3:
            r = (~r) & FULL
        pool.append(r)
    return pool[-1]


def tt_to_bits(v):
    return np.array([(v >> a) & 1 for a in range(N)], dtype=np.int64)


# ---------- efficient features ----------
def butterfly(a):
    a = a.astype(np.float64).copy()
    h = 1
    while h < N:
        for i in range(0, N, h * 2):
            blk = a[i:i + 2 * h]
            x = blk[:h].copy(); y = blk[h:].copy()
            a[i:i + h] = x + y
            a[i + h:i + 2 * h] = x - y
        h *= 2
    return a


def anf_degree(bits):
    a = bits.copy()
    h = 1
    while h < N:
        for i in range(0, N, h * 2):
            a[i + h:i + 2 * h] ^= a[i:i + h]
        h *= 2
    deg = 0
    for idx in range(N):
        if a[idx]:
            deg = max(deg, bin(idx).count("1"))
    return deg


POP = [bin(i).count("1") for i in range(N)]


def features(v):
    bits = tt_to_bits(v)
    chi = 1.0 - 2.0 * bits
    coeff = butterfly(chi) / N
    c2 = coeff ** 2
    total_inf = float(sum(c2[i] * POP[i] for i in range(N)))
    spec = c2.copy(); spec[0] = 0.0
    max_deg = max((POP[i] for i in range(N) if abs(coeff[i]) > 1e-9), default=0)
    sparsity = int(np.sum(np.abs(coeff) > 1e-9))
    l1 = float(np.sum(np.abs(coeff)))
    weight = float(bits.mean())
    alg_deg = anf_degree(bits)
    # single-coordinate influences (degree-1 mass per variable)
    return np.array([
        total_inf,                # average sensitivity
        max_deg,                  # Fourier degree
        sparsity,                 # Fourier sparsity
        l1,                       # spectral norm
        alg_deg,                  # algebraic (ANF) degree
        abs(weight - 0.5),        # bias
        float(np.max(c2[1:])),    # largest non-trivial Fourier mass
    ], dtype=np.float64)

FEAT_NAMES = ["avg_sens", "fourier_deg", "sparsity", "spectral_L1",
              "anf_deg", "bias", "max_fourier_mass"]


# ---------- datasets ----------
def build():
    random.seed(1)
    easy = [random_circuit_tt(random.randint(1, 5)) for _ in range(500)]
    rand = [random.getrandbits(N) for _ in range(500)]
    scramble = [random_circuit_tt(random.randint(8, 16), xor_heavy=True)
                for _ in range(500)]
    return easy, rand, scramble


def feat_matrix(fns):
    return np.array([features(v) for v in fns])


def standardize(X, mu, sd):
    return (X - mu) / sd


def auc(scores_pos, scores_neg):
    # P(score_pos > score_neg)
    pos = np.sort(scores_pos)
    wins = 0
    for s in scores_neg:
        wins += np.searchsorted(pos, s, side="left")
    return 1.0 - wins / (len(pos) * len(scores_neg))


# ---------- evolve mu = w . standardized_features ----------
def evolve(Xe, Xr, gens=60, pop=40, seed=0):
    rng = np.random.default_rng(seed)
    d = Xe.shape[1]
    population = [rng.normal(size=d) for _ in range(pop)]

    def fit(w):
        return auc(Xr @ w, Xe @ w)   # want random high, easy low

    for _ in range(gens):
        population.sort(key=fit, reverse=True)
        survivors = population[: pop // 3]
        children = []
        while len(survivors) + len(children) < pop:
            p = survivors[rng.integers(len(survivors))].copy()
            p += rng.normal(scale=0.4, size=d)
            children.append(p)
        population = survivors + children
    population.sort(key=fit, reverse=True)
    return population[0]


if __name__ == "__main__":
    easy, rand, scramble = build()
    Xe, Xr, Xs = feat_matrix(easy), feat_matrix(rand), feat_matrix(scramble)
    mu = np.concatenate([Xe, Xr]).mean(0)
    sd = np.concatenate([Xe, Xr]).std(0) + 1e-9
    Ze, Zr, Zs = (standardize(X, mu, sd) for X in (Xe, Xr, Xs))

    # train/test split
    tr = slice(0, 350); te = slice(350, 500)
    w = evolve(Ze[tr], Zr[tr])

    se_tr, sr_tr = Ze[tr] @ w, Zr[tr] @ w
    se_te, sr_te = Ze[te] @ w, Zr[te] @ w
    ss = Zs @ w

    thr = 0.5 * (np.median(se_tr) + np.median(sr_tr))  # easy<thr<random
    frac_rand_hard = float(np.mean(Zr @ w > thr))
    frac_scram_hard = float(np.mean(ss > thr))
    frac_easy_hard = float(np.mean(Ze @ w > thr))

    print("Evolved measure mu = w . features")
    print("  weights:", {nm: round(float(wi), 2) for nm, wi in zip(FEAT_NAMES, w)})
    print()
    print(f"  TRAIN  AUC(easy vs random)      : {auc(sr_tr, se_tr):.3f}")
    print(f"  TEST   AUC(easy vs random)      : {auc(sr_te, se_te):.3f}   <- generalises?")
    print()
    print("  LARGENESS / naturalness check (fraction flagged 'hard'):")
    print(f"    random  functions flagged hard: {frac_rand_hard:.3f}")
    print(f"    easy    functions flagged hard: {frac_easy_hard:.3f}")
    print()
    print("  DECISIVE test -- scramble = SMALL-CIRCUIT (in P) but random-looking:")
    print(f"    AUC(easy vs scramble)         : {auc(ss, se_te):.3f}")
    print(f"    scramble flagged HARD          : {frac_scram_hard:.3f}"
          "   <- these are EASY; a real P-vs-NP measure must keep them LOW")
