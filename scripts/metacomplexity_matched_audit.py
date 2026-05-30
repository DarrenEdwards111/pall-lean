#!/usr/bin/env python3
"""
Local-feature-matched compressed-vs-random audit.

The earlier audits showed that local/structural features classify the toy
"hard-looking" sets too well.  This script tries to remove that confound:

1. Generate compressed n=4 functions from short construction families.
2. Generate random n=4 truth tables.
3. Greedily match compressed/random functions by local feature signature.
4. Train/test linear invariants on the matched set.

If compression/K^t features beat structural features after local matching, that
is genuine empirical evidence for a metacomplexity signal.  If structural
features still win, the audit has not isolated metacomplexity.
"""

from __future__ import annotations

import argparse
import random
from collections import defaultdict

from evolve_boolean_invariant_search import (
    algebraic_degree,
    anf_sparsity,
    certificate_complexity,
    decision_tree_depth,
    evolve,
    f_and,
    f_maj,
    f_or,
    f_xor,
    full_mask,
    junta_size,
    monotone_violations,
    popcount,
    sensitivity_values,
    var_mask,
    walsh_spectrum,
)
from kt_complexity import compositional_kt_upper_bounds


def bit(mask: int, i: int) -> int:
    return (mask >> i) & 1


def truth_mask(n: int, pred) -> int:
    mask = 0
    for x in range(1 << n):
        bits = [(x >> j) & 1 for j in range(n)]
        if pred(bits):
            mask |= 1 << x
    return mask


def threshold_mask(n: int, t: int) -> int:
    return truth_mask(n, lambda bits: sum(bits) >= t)


def affine_masks(n: int) -> set[int]:
    masks = set()
    for coeff in range(1 << n):
        for c in (0, 1):
            masks.add(truth_mask(n, lambda bits, coeff=coeff, c=c:
                                 (sum(bits[j] for j in range(n) if (coeff >> j) & 1) + c) % 2 == 1))
    return masks


def random_quadratic_mask(n: int, rng: random.Random, terms: int) -> int:
    linear = [j for j in range(n)]
    quad = [(i, j) for i in range(n) for j in range(i + 1, n)]
    choices = [("lin", j) for j in linear] + [("quad", p) for p in quad]
    chosen = rng.sample(choices, min(terms, len(choices)))
    c = rng.randrange(2)

    def pred(bits):
        acc = c
        for kind, data in chosen:
            if kind == "lin":
                acc ^= bits[data]
            else:
                i, j = data
                acc ^= bits[i] & bits[j]
        return acc == 1

    return truth_mask(n, pred)


def random_dnf_mask(n: int, rng: random.Random, clauses: int, width: int) -> int:
    terms = []
    for _ in range(clauses):
        vars_ = rng.sample(range(n), width)
        signs = [rng.randrange(2) for _ in vars_]
        terms.append(list(zip(vars_, signs)))

    def pred(bits):
        for term in terms:
            if all(bits[j] == s for j, s in term):
                return True
        return False

    return truth_mask(n, pred)


def lfsr_mask(n: int, seed: int, taps=(0, 1)) -> int:
    state = seed & 0b1111
    if state == 0:
        state = 1
    mask = 0
    for i in range(1 << n):
        out = state & 1
        if out:
            mask |= 1 << i
        fb = 0
        for t in taps:
            fb ^= (state >> t) & 1
        state = ((state >> 1) | (fb << 3)) & 0b1111
        if state == 0:
            state = 1
    return mask


def cellular_automaton_mask(n: int, rule: int, seed: int) -> int:
    width = n
    state = [(seed >> j) & 1 for j in range(width)]
    mask = 0
    for i in range(1 << n):
        if state[0]:
            mask |= 1 << i
        nxt = []
        for j in range(width):
            left = state[(j - 1) % width]
            mid = state[j]
            right = state[(j + 1) % width]
            idx = (left << 2) | (mid << 1) | right
            nxt.append((rule >> idx) & 1)
        state = nxt
    return mask


def named_easy_masks(n: int) -> set[int]:
    masks = {0, full_mask(n), f_and(n), f_or(n), f_maj(n), f_xor(n)}
    for j in range(n):
        masks.add(var_mask(n, j))
        masks.add(full_mask(n) ^ var_mask(n, j))
    masks |= {threshold_mask(n, t) for t in range(1, n + 1)}
    masks |= affine_masks(n)
    return masks


def generate_compressed(n: int, rng: random.Random, args) -> set[int]:
    masks = set(named_easy_masks(n))
    for _ in range(args.quadratic_samples):
        masks.add(random_quadratic_mask(n, rng, rng.randint(2, 5)))
    for _ in range(args.dnf_samples):
        masks.add(random_dnf_mask(n, rng, clauses=rng.randint(1, 5), width=rng.randint(1, 3)))
    for rule in args.ca_rules:
        for seed in range(1, 1 << n):
            masks.add(cellular_automaton_mask(n, rule, seed))
    for seed in range(1, 1 << n):
        masks.add(lfsr_mask(n, seed))
    return masks


def local_raw_features(mask: int, n: int) -> dict[str, float]:
    sens = sensitivity_values(mask, n)
    walsh = walsh_spectrum(mask, n)
    weight = popcount(mask)
    return {
        "weight": weight,
        "balance": abs(weight - (1 << (n - 1))),
        "anf_degree": algebraic_degree(mask, n),
        "anf_sparsity": anf_sparsity(mask, n),
        "max_sensitivity": max(sens),
        "avg_sensitivity": sum(sens) / len(sens),
        "decision_tree_depth": decision_tree_depth(mask, n),
        "certificate_complexity": certificate_complexity(mask, n),
        "walsh_max_abs": max(abs(x) for x in walsh),
        "walsh_support": sum(1 for x in walsh if x != 0),
        "junta_size": junta_size(mask, n),
        "monotone_violations": monotone_violations(mask, n),
    }


def local_signature(mask: int, n: int) -> tuple:
    f = local_raw_features(mask, n)
    return (
        f["weight"],
        f["balance"],
        f["anf_degree"],
        f["anf_sparsity"],
        f["max_sensitivity"],
        round(f["avg_sensitivity"], 3),
        f["decision_tree_depth"],
        f["certificate_complexity"],
        f["walsh_max_abs"],
        f["walsh_support"],
        f["junta_size"],
    )


def local_distance(a: dict[str, float], b: dict[str, float]) -> float:
    keys = list(a.keys())
    return sum(abs(a[k] - b[k]) for k in keys)


def min_period_length(bits: list[int]) -> int:
    L = len(bits)
    for p in range(1, L + 1):
        if L % p == 0 and all(bits[i] == bits[i % p] for i in range(L)):
            return p
    return L


def lz_complexity(bits: list[int]) -> int:
    seen = set()
    i = 0
    phrases = 0
    while i < len(bits):
        j = i + 1
        while j <= len(bits) and tuple(bits[i:j]) in seen:
            j += 1
        seen.add(tuple(bits[i:min(j, len(bits))]))
        phrases += 1
        i = j
    return phrases


def greedy_match(n: int, compressed: set[int], randoms: set[int], args):
    random_by_sig = defaultdict(list)
    for m in randoms:
        random_by_sig[local_signature(m, n)].append(m)

    pairs = []
    used_random = set()
    compressed_list = list(compressed)
    random_list = list(randoms)
    random_features = {m: local_raw_features(m, n) for m in random_list}

    for c in compressed_list:
        sig = local_signature(c, n)
        exacts = [m for m in random_by_sig.get(sig, []) if m not in used_random]
        if exacts:
            r = exacts[0]
            pairs.append((c, r, 0.0))
            used_random.add(r)
            continue
        cf = local_raw_features(c, n)
        best = None
        for r in random_list:
            if r in used_random:
                continue
            d = local_distance(cf, random_features[r])
            if best is None or d < best[0]:
                best = (d, r)
        if best is not None and best[0] <= args.max_match_distance:
            pairs.append((c, best[1], best[0]))
            used_random.add(best[1])
    pairs.sort(key=lambda x: x[2])
    return pairs[:args.max_pairs]


def feature_table(n: int, masks: list[int], comp_xor: dict[int, int], comp_cost: int):
    names = [
        "weight",
        "balance",
        "anf_degree",
        "anf_sparsity",
        "max_sensitivity",
        "avg_sensitivity",
        "decision_tree_depth",
        "certificate_complexity",
        "walsh_max_abs",
        "walsh_support",
        "junta_size",
        "monotone_violations",
        "period_min",
        "lz_complexity",
        "bounded_comp_kt_xor",
    ]
    rows = []
    for m in masks:
        local = local_raw_features(m, n)
        bits = [bit(m, i) for i in range(1 << n)]
        rows.append([
            local["weight"],
            local["balance"],
            local["anf_degree"],
            local["anf_sparsity"],
            local["max_sensitivity"],
            local["avg_sensitivity"],
            local["decision_tree_depth"],
            local["certificate_complexity"],
            local["walsh_max_abs"],
            local["walsh_support"],
            local["junta_size"],
            local["monotone_violations"],
            min_period_length(bits),
            lz_complexity(bits),
            min(comp_xor.get(m, 1 << n), comp_cost + 1),
        ])
    maxima = [max(abs(row[i]) for row in rows) or 1 for i in range(len(names))]
    norm = [[row[i] / maxima[i] for i in range(len(names))] for row in rows]
    return names, norm


def signed_scores(best, features):
    raw = [
        sum(w * x for w, x in zip(best.weights, row))
        for row in features
    ]
    return [best.polarity * s for s in raw], best.polarity * best.threshold


def evaluate_fixed(best, features, compressed_i, random_i):
    scores, threshold = signed_scores(best, features)
    comp_correct = sum(scores[i] < threshold for i in compressed_i)
    rand_correct = sum(scores[i] >= threshold for i in random_i)
    acc = (comp_correct + rand_correct) / (len(compressed_i) + len(random_i))
    bacc = 0.5 * (comp_correct / len(compressed_i) + rand_correct / len(random_i))
    rand_min = min(scores[i] for i in random_i)
    comp_max = max(scores[i] for i in compressed_i)
    density = sum(s >= threshold for s in scores) / len(scores)
    return acc, bacc, rand_min - comp_max, density


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def run(args) -> None:
    n = args.n
    rng = random.Random(args.seed)
    compressed = generate_compressed(n, rng, args)
    randoms = set()
    while len(randoms) < args.random_samples:
        m = rng.randrange(1 << (1 << n))
        if m not in compressed:
            randoms.add(m)

    pairs = greedy_match(n, compressed, randoms, args)
    if len(pairs) < 4:
        raise SystemExit("not enough matched pairs; increase random_samples or max_match_distance")

    matched_compressed = [c for c, _r, _d in pairs]
    matched_random = [r for _c, r, _d in pairs]
    masks = matched_compressed + matched_random
    compressed_i = set(range(len(matched_compressed)))
    random_i = set(range(len(matched_compressed), len(masks)))
    distances = [d for _c, _r, d in pairs]

    comp_xor = compositional_kt_upper_bounds(n, max_cost=args.comp_cost, include_xor=True)
    names, features = feature_table(n, masks, comp_xor, args.comp_cost)
    groups = {
        "local": [i for i, name in enumerate(names)
                  if name not in {"period_min", "lz_complexity", "bounded_comp_kt_xor"}],
        "compress": [i for i, name in enumerate(names)
                     if name in {"period_min", "lz_complexity", "bounded_comp_kt_xor"}],
        "all": list(range(len(names))),
    }

    print("=" * 104)
    print("Matched compressed-vs-random metacomplexity audit")
    print("=" * 104)
    print(f"n={n}, compressed_pool={len(compressed)}, random_pool={len(randoms)}, matched_pairs={len(pairs)}")
    print(
        f"match distance: mean={mean(distances):.3f}, "
        f"median={sorted(distances)[len(distances)//2]:.3f}, max={max(distances):.3f}"
    )
    print(f"bounded comp+XOR table size={len(comp_xor)}")
    print()

    rng = random.Random(args.seed + 1)
    for label in ("local", "compress", "all"):
        train_accs, test_accs, train_baccs, test_baccs, train_margins, test_margins, densities = [], [], [], [], [], [], []
        indices = list(range(len(pairs)))
        for trial in range(args.trials):
            rng.shuffle(indices)
            cut = max(1, len(indices) // 2)
            train_pairs = indices[:cut]
            test_pairs = indices[cut:]
            train_comp = {i for i in train_pairs}
            train_rand = {i + len(pairs) for i in train_pairs}
            test_comp = {i for i in test_pairs}
            test_rand = {i + len(pairs) for i in test_pairs}
            best = evolve(
                names,
                features,
                train_comp,
                train_rand,
                groups[label],
                seed=args.seed + 1000 + trial * 41 + len(label),
                population=args.population,
                generations=args.generations,
                verbose=False,
            )
            tr_acc, tr_bacc, tr_margin, density = evaluate_fixed(best, features, train_comp, train_rand)
            te_acc, te_bacc, te_margin, _ = evaluate_fixed(best, features, test_comp, test_rand)
            train_accs.append(tr_acc)
            train_baccs.append(tr_bacc)
            train_margins.append(tr_margin)
            test_accs.append(te_acc)
            test_baccs.append(te_bacc)
            test_margins.append(te_margin)
            densities.append(density)
        print(
            f"  {label:<8} train_acc={mean(train_accs):.3f} "
            f"test_acc={mean(test_accs):.3f} "
            f"train_bacc={mean(train_baccs):.3f} "
            f"test_bacc={mean(test_baccs):.3f} "
            f"train_margin={mean(train_margins):.3f} "
            f"test_margin={mean(test_margins):.3f} "
            f"density={mean(densities):.3f}"
        )

    print()
    print("Reading:")
    print("  local near chance + compression above chance = isolated metacomplexity signal.")
    print("  local still strong = matching was insufficient or local structure still carries the split.")
    print("  all much better than both = possible interaction worth investigating.")


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=4)
    parser.add_argument("--seed", type=int, default=20260528)
    parser.add_argument("--population", type=int, default=35)
    parser.add_argument("--generations", type=int, default=16)
    parser.add_argument("--trials", type=int, default=12)
    parser.add_argument("--quadratic-samples", type=int, default=250)
    parser.add_argument("--dnf-samples", type=int, default=250)
    parser.add_argument("--ca-rules", type=int, nargs="+", default=[30, 45, 90, 105, 110, 150])
    parser.add_argument("--random-samples", type=int, default=3000)
    parser.add_argument("--max-match-distance", type=float, default=6.0)
    parser.add_argument("--max-pairs", type=int, default=180)
    parser.add_argument("--comp-cost", type=int, default=7)
    return parser.parse_args()


if __name__ == "__main__":
    run(parse_args())
