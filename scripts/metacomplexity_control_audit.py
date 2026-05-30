#!/usr/bin/env python3
"""
Control audits for the metacomplexity invariant search.

The first frontier audit found a warning sign: at n=3, local/structural
features often classify the toy "easy vs hard-looking" split as well as
MCSP/K^t features.  This script adds three controls:

1. Random-label baseline.  If the evolutionary search can generalize random
   labels, the feature family is too expressive for the toy universe.
2. Cross-threshold transfer.  Train on one MCSP/K^t cutoff and test the fixed
   invariant on other cutoffs.
3. Sampled n=4 families.  Exact MCSP is not feasible over all 2^16 Boolean
   functions here, so we use bounded compositional K^t and construction-family
   controls over sampled simple, affine/quadratic, and random functions.

This is a diagnostic only.  It does not prove P != NP and does not produce a
barrier-evading invariant.
"""

from __future__ import annotations

import argparse
import random
from collections import defaultdict

from evolve_boolean_invariant_search import (
    NOT,
    algebraic_degree,
    anf_coefficients,
    anf_sparsity,
    certificate_complexity,
    decision_tree_depth,
    describe,
    evolve,
    f_and,
    f_maj,
    f_or,
    f_xor,
    feature_table,
    full_mask,
    junta_size,
    monotone_violations,
    named_easy_masks,
    popcount,
    sensitivity_values,
    var_mask,
    walsh_spectrum,
)
from kt_complexity import compositional_kt_upper_bounds
from metacomplexity import AND, OR, num_funcs


def feature_groups(names: list[str]) -> dict[str, list[int]]:
    return {
        "struct": [i for i, name in enumerate(names) if name not in {"mcsp", "comp_kt", "comp_kt_xor"}],
        "meta": [i for i, name in enumerate(names) if name in {"mcsp", "comp_kt", "comp_kt_xor"}],
        "kt": [i for i, name in enumerate(names) if name in {"comp_kt", "comp_kt_xor"}],
        "all": list(range(len(names))),
    }


def target_sets(n: int, mcsp, comp_xor, easy_kt: int, hard_mcsp: int, hard_kt: int):
    easy = set(named_easy_masks(n))
    easy |= {m for m in range(num_funcs(n)) if comp_xor.get(m, 1 << n) <= easy_kt}
    hard = {
        m for m in range(num_funcs(n))
        if mcsp[m] >= hard_mcsp and comp_xor.get(m, 1 << n) >= hard_kt
    }
    hard -= easy
    return easy, hard


def signed_scores(best, features):
    raw = [
        sum(w * x for w, x in zip(best.weights, row))
        for row in features
    ]
    return [best.polarity * s for s in raw], best.polarity * best.threshold


def evaluate_fixed(best, features, easy, hard):
    acc, _bacc, margin, density = evaluate_fixed_detail(best, features, easy, hard)
    return acc, margin, density


def evaluate_fixed_detail(best, features, easy, hard):
    scores, threshold = signed_scores(best, features)
    total = len(easy) + len(hard)
    easy_correct = 0
    hard_correct = 0
    for m in easy:
        easy_correct += scores[m] < threshold
    for m in hard:
        hard_correct += scores[m] >= threshold
    hard_min = min(scores[m] for m in hard)
    easy_max = max(scores[m] for m in easy)
    density = sum(1 for s in scores if s >= threshold) / len(scores)
    acc = (easy_correct + hard_correct) / total
    bacc = 0.5 * (easy_correct / len(easy) + hard_correct / len(hard))
    return acc, bacc, hard_min - easy_max, density


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def random_label_baseline(args, names, features, groups, easy_size: int, hard_size: int) -> None:
    rng = random.Random(args.seed + 101)
    universe = list(range(num_funcs(3)))
    print("=" * 104)
    print("1. Random-label baseline")
    print("=" * 104)
    majority_baseline = max(easy_size, hard_size) / (easy_size + hard_size)
    print(
        f"labels per trial: easy={easy_size}, hard={hard_size}; "
        "train/test split is 50/50 within each random label class"
    )
    print(f"class-imbalance accuracy baseline: {majority_baseline:.3f}; balanced baseline: 0.500")
    for label in ("struct", "meta", "all"):
        train_accs, test_accs, train_baccs, test_baccs, train_margins, test_margins = [], [], [], [], [], []
        for trial in range(args.random_trials):
            rng.shuffle(universe)
            easy = set(universe[:easy_size])
            hard = set(universe[easy_size:easy_size + hard_size])
            easy_list = sorted(easy)
            hard_list = sorted(hard)
            rng.shuffle(easy_list)
            rng.shuffle(hard_list)
            train_easy = set(easy_list[: max(1, len(easy_list) // 2)])
            test_easy = set(easy_list[max(1, len(easy_list) // 2):])
            train_hard = set(hard_list[: max(1, len(hard_list) // 2)])
            test_hard = set(hard_list[max(1, len(hard_list) // 2):])
            if not test_easy or not test_hard:
                continue
            best = evolve(
                names,
                features,
                train_easy,
                train_hard,
                groups[label],
                seed=args.seed + 1000 + trial * 17 + len(label),
                population=args.population,
                generations=args.generations,
                verbose=False,
            )
            tr_acc, tr_bacc, tr_margin, _ = evaluate_fixed_detail(best, features, train_easy, train_hard)
            te_acc, te_bacc, te_margin, _ = evaluate_fixed_detail(best, features, test_easy, test_hard)
            train_accs.append(tr_acc)
            train_baccs.append(tr_bacc)
            train_margins.append(tr_margin)
            test_accs.append(te_acc)
            test_baccs.append(te_bacc)
            test_margins.append(te_margin)
        print(
            f"  {label:<6} train_acc={mean(train_accs):.3f} "
            f"test_acc={mean(test_accs):.3f} "
            f"train_bacc={mean(train_baccs):.3f} "
            f"test_bacc={mean(test_baccs):.3f} "
            f"train_margin={mean(train_margins):.3f} "
            f"test_margin={mean(test_margins):.3f}"
        )
    print("  Reading: balanced accuracy near 0.5 means the search is not learning arbitrary labels.")
    print()


def cross_threshold_transfer(args, names, features, mcsp, comp_xor, groups) -> None:
    configs = []
    for easy_kt in (4, 5):
        for hard_mcsp in (7, 8, 9):
            for hard_kt in (6, 7, 8):
                easy, hard = target_sets(3, mcsp, comp_xor, easy_kt, hard_mcsp, hard_kt)
                if hard:
                    configs.append((easy_kt, hard_mcsp, hard_kt, easy, hard))

    train_easy, train_hard = target_sets(
        3, mcsp, comp_xor, args.train_easy_kt, args.train_hard_mcsp, args.train_hard_kt
    )
    print("=" * 104)
    print("2. Cross-threshold transfer")
    print("=" * 104)
    print(
        f"train config: easy_kt<={args.train_easy_kt}, "
        f"hard_mcsp>={args.train_hard_mcsp}, hard_kt>={args.train_hard_kt}; "
        f"easy={len(train_easy)}, hard={len(train_hard)}"
    )
    for label in ("struct", "meta", "all"):
        best = evolve(
            names,
            features,
            train_easy,
            train_hard,
            groups[label],
            seed=args.seed + 2000 + len(label),
            population=args.population,
            generations=args.generations,
            verbose=False,
        )
        accs, margins = [], []
        baccs = []
        for _easy_kt, _hard_mcsp, _hard_kt, easy, hard in configs:
            acc, bacc, margin, _ = evaluate_fixed_detail(best, features, easy, hard)
            accs.append(acc)
            baccs.append(bacc)
            margins.append(margin)
        print(
            f"  {label:<6} train={describe(best, names)}\n"
            f"         transfer_acc={mean(accs):.3f} "
            f"transfer_bacc={mean(baccs):.3f} min_bacc={min(baccs):.3f} "
            f"min_acc={min(accs):.3f} transfer_margin={mean(margins):.3f} "
            f"min_margin={min(margins):.3f}"
        )
    print("  Reading: brittle transfer means the toy invariant is cutoff-specific.")
    print()


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


def sample_n4_masks(args):
    n = 4
    rng = random.Random(args.seed + 303)
    easy = set(named_easy_masks(n))
    easy |= {threshold_mask(n, t) for t in range(1, n + 1)}
    easy |= affine_masks(n)
    for _ in range(args.n4_easy_quadratic):
        easy.add(random_quadratic_mask(n, rng, rng.randint(2, 5)))
    for _ in range(args.n4_easy_dnf):
        easy.add(random_dnf_mask(n, rng, clauses=rng.randint(1, 4), width=rng.randint(1, 2)))

    comp_xor = compositional_kt_upper_bounds(n, max_cost=args.n4_comp_cost, include_xor=True)
    low_comp = [m for m, c in comp_xor.items() if c <= args.n4_easy_comp_cost]
    rng.shuffle(low_comp)
    easy |= set(low_comp[:args.n4_easy_comp_samples])

    hard = set()
    attempts = 0
    while len(hard) < args.n4_hard_random and attempts < args.n4_hard_random * 200:
        attempts += 1
        m = rng.randrange(1 << (1 << n))
        if m in easy:
            continue
        if comp_xor.get(m, 1 << n) <= args.n4_easy_comp_cost:
            continue
        hard.add(m)

    masks = sorted(easy | hard)
    index = {m: i for i, m in enumerate(masks)}
    easy_i = {index[m] for m in easy if m in index}
    hard_i = {index[m] for m in hard if m in index}
    return masks, easy_i, hard_i, comp_xor


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


def sampled_feature_table(n: int, masks: list[int], comp_xor: dict[int, int], comp_cost: int):
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
        bits = [(m >> i) & 1 for i in range(1 << n)]
        sens = sensitivity_values(m, n)
        walsh = walsh_spectrum(m, n)
        weight = popcount(m)
        rows.append([
            weight,
            abs(weight - (1 << (n - 1))),
            algebraic_degree(m, n),
            anf_sparsity(m, n),
            max(sens),
            sum(sens) / len(sens),
            decision_tree_depth(m, n),
            certificate_complexity(m, n),
            max(abs(x) for x in walsh),
            sum(1 for x in walsh if x != 0),
            junta_size(m, n),
            monotone_violations(m, n),
            min_period_length(bits),
            lz_complexity(bits),
            min(comp_xor.get(m, 1 << n), comp_cost + 1),
        ])
    maxima = [max(abs(row[i]) for row in rows) or 1 for i in range(len(names))]
    norm = [[row[i] / maxima[i] for i in range(len(names))] for row in rows]
    return names, norm


def sampled_n4_audit(args) -> None:
    masks, easy, hard, comp_xor = sample_n4_masks(args)
    names, features = sampled_feature_table(4, masks, comp_xor, args.n4_comp_cost)
    groups = {
        "local": [i for i, name in enumerate(names) if name not in {"period_min", "lz_complexity", "bounded_comp_kt_xor"}],
        "compress": [i for i, name in enumerate(names) if name in {"period_min", "lz_complexity", "bounded_comp_kt_xor"}],
        "all": list(range(len(names))),
    }
    rng = random.Random(args.seed + 404)
    print("=" * 104)
    print("3. Sampled n=4 family audit")
    print("=" * 104)
    print(
        f"samples={len(masks)}, easy={len(easy)}, hard={len(hard)}, "
        f"bounded comp+XOR functions={len(comp_xor)}"
    )
    print("easy includes named/affine/quadratic/DNF/low-compositional samples; hard is random non-low-comp.")
    for label in ("local", "compress", "all"):
        train_accs, test_accs, train_baccs, test_baccs, train_margins, test_margins, densities = [], [], [], [], [], [], []
        easy_list = sorted(easy)
        hard_list = sorted(hard)
        for trial in range(args.n4_trials):
            rng.shuffle(easy_list)
            rng.shuffle(hard_list)
            ec = max(1, len(easy_list) // 2)
            hc = max(1, len(hard_list) // 2)
            train_easy = set(easy_list[:ec])
            test_easy = set(easy_list[ec:])
            train_hard = set(hard_list[:hc])
            test_hard = set(hard_list[hc:])
            best = evolve(
                names,
                features,
                train_easy,
                train_hard,
                groups[label],
                seed=args.seed + 7000 + trial * 19 + len(label),
                population=args.population,
                generations=args.generations,
                verbose=False,
            )
            tr_acc, tr_bacc, tr_margin, density = evaluate_fixed_detail(best, features, train_easy, train_hard)
            te_acc, te_bacc, te_margin, _ = evaluate_fixed_detail(best, features, test_easy, test_hard)
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
    print("  Reading: if local still wins, the audit is still seeing random-vs-structured structure, not P vs NP.")
    print()


def run(args) -> None:
    names, _raw, features, mcsp, comp_xor = feature_table(3)
    groups = feature_groups(names)
    easy, hard = target_sets(3, mcsp, comp_xor, args.train_easy_kt, args.train_hard_mcsp, args.train_hard_kt)

    print("=" * 104)
    print("Metacomplexity control audit")
    print("=" * 104)
    print("This script checks whether the earlier toy signal survives stronger controls.")
    print()

    random_label_baseline(args, names, features, groups, len(easy), len(hard))
    cross_threshold_transfer(args, names, features, mcsp, comp_xor, groups)
    sampled_n4_audit(args)


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--population", type=int, default=35)
    parser.add_argument("--generations", type=int, default=14)
    parser.add_argument("--seed", type=int, default=20260528)
    parser.add_argument("--random-trials", type=int, default=12)
    parser.add_argument("--train-easy-kt", type=int, default=5)
    parser.add_argument("--train-hard-mcsp", type=int, default=8)
    parser.add_argument("--train-hard-kt", type=int, default=7)
    parser.add_argument("--n4-comp-cost", type=int, default=7)
    parser.add_argument("--n4-easy-comp-cost", type=int, default=5)
    parser.add_argument("--n4-easy-comp-samples", type=int, default=120)
    parser.add_argument("--n4-easy-quadratic", type=int, default=80)
    parser.add_argument("--n4-easy-dnf", type=int, default=80)
    parser.add_argument("--n4-hard-random", type=int, default=260)
    parser.add_argument("--n4-trials", type=int, default=10)
    return parser.parse_args()


if __name__ == "__main__":
    run(parse_args())
