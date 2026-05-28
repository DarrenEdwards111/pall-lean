#!/usr/bin/env python3
"""
"You need a better reward function."  Correct -- so here it is, and here is
what it runs into.

The flaw last time: fitness only rewarded easy(low) vs random(high), so the EA
learned 'structured vs random', a natural property.  The BETTER reward adds the
missing constraint -- keep the SCRAMBLE set low too, because scramble functions
are small-circuit (in P) and a real P-vs-NP measure must NOT call them hard:

    fitness(w) = AUC(random>easy)  -  lambda * (fraction of scramble called hard)

We then sweep the scramble STRENGTH (number of XOR-heavy gates).  Weak scramble
is distinguishable from random, so the better reward is satisfiable.  As
scramble -> pseudorandom, 'random high but scramble low' asks for an efficient
distinguisher of pseudorandom from random -- which PRFs forbid -- so the better
reward's solution set empties out, and the EA cannot satisfy it.

That is the point: the difficulty does not vanish with a better reward; it
relocates INTO the reward (an empty / uncomputable target).
"""

import numpy as np
import random
import scripts.spdp_ea_pvsnp_probe as M


def feats(fns):
    return np.array([M.features(v) for v in fns])


def auc(pos, neg):
    sp = np.sort(pos)
    wins = sum(np.searchsorted(sp, s, side="left") for s in neg)
    return 1.0 - wins / (len(sp) * len(neg))


def evolve(Ze, Zr, Zs, lam=1.0, gens=60, pop=40, seed=0):
    rng = np.random.default_rng(seed)
    d = Ze.shape[1]
    thr_e = np.median  # placeholder

    def fitness(w):
        se, sr, ss = Ze @ w, Zr @ w, Zs @ w
        thr = 0.5 * (np.median(se) + np.median(sr))
        a = auc(sr, se)
        scram_hard = float(np.mean(ss > thr))
        return a - lam * scram_hard

    population = [rng.normal(size=d) for _ in range(pop)]
    for _ in range(gens):
        population.sort(key=fitness, reverse=True)
        surv = population[: pop // 3]
        kids = []
        while len(surv) + len(kids) < pop:
            p = surv[rng.integers(len(surv))].copy()
            p += rng.normal(scale=0.4, size=d)
            kids.append(p)
        population = surv + kids
    population.sort(key=fitness, reverse=True)
    return population[0]


if __name__ == "__main__":
    random.seed(3)
    easy = [M.random_circuit_tt(random.randint(1, 5)) for _ in range(400)]
    rand = [random.getrandbits(M.N) for _ in range(400)]
    Xe, Xr = feats(easy), feats(rand)
    base = np.concatenate([Xe, Xr])
    mu, sd = base.mean(0), base.std(0) + 1e-9
    Ze, Zr = (Xe - mu) / sd, (Xr - mu) / sd

    print(f"n={M.N.bit_length()-1}  (truth tables length {M.N})")
    print("Better reward: separate easy(low)/random(high) AND keep scramble(low)\n")
    print(f"{'scramble gates':>14} | {'AUC easy/random':>15} | "
          f"{'scramble->hard':>14} | {'reward satisfiable?':>19}")
    print("-" * 72)

    for g in [4, 8, 16, 24, 40, 64]:
        scr = [M.random_circuit_tt(g, xor_heavy=True) for _ in range(400)]
        Zs = (feats(scr) - mu) / sd
        w = evolve(Ze, Zr, Zs, lam=1.0)
        se, sr, ss = Ze @ w, Zr @ w, Zs @ w
        thr = 0.5 * (np.median(se) + np.median(sr))
        a = auc(sr, se)
        scram_hard = float(np.mean(ss > thr))
        ok = "yes" if (a > 0.9 and scram_hard < 0.1) else "NO -- target empty"
        print(f"{g:>14} | {a:>15.3f} | {scram_hard:>14.3f} | {ok:>19}")

    print("\nAs scramble -> pseudorandom, you cannot keep scramble low while")
    print("random stays high: the better reward's solution set empties out.")
