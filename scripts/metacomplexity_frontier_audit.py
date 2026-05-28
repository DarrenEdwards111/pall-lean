#!/usr/bin/env python3
"""
Sweep the small Boolean-function universe for metacomplexity-style invariant
signals.

This is a diagnostic, not a P-vs-NP proof.  The goal is to answer a narrower
question: when we ask an evolutionary search to separate easy/P-like toy
functions from high-MCSP/high-K^t toy functions, which feature families carry
the signal?

The useful outcome is negative/positive in a precise sense:

* If structural/local features win with high density, the signal is natural-ish
  and unlikely to survive the known barriers.
* If MCSP/K^t features are necessary for sparse separation, the signal points
  back to the metacomplexity frontier rather than a simple rank/local invariant.
"""

from __future__ import annotations

import argparse
import random

from evolve_boolean_invariant_search import (
    describe,
    evolve,
    feature_table,
    named_easy_masks,
)
from metacomplexity import num_funcs


def feature_groups(names: list[str]) -> dict[str, list[int]]:
    structural = [i for i, name in enumerate(names) if name not in {"mcsp", "comp_kt", "comp_kt_xor"}]
    meta_only = [i for i, name in enumerate(names) if name in {"mcsp", "comp_kt", "comp_kt_xor"}]
    kt_only = [i for i, name in enumerate(names) if name in {"comp_kt", "comp_kt_xor"}]
    no_mcsp = [i for i, name in enumerate(names) if name != "mcsp"]
    no_kt = [i for i, name in enumerate(names) if name not in {"comp_kt", "comp_kt_xor"}]
    all_features = list(range(len(names)))
    return {
        "struct": structural,
        "meta": meta_only,
        "kt": kt_only,
        "no_mcsp": no_mcsp,
        "no_kt": no_kt,
        "all": all_features,
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


def run(args) -> None:
    names, _raw, features, mcsp, comp_xor = feature_table(args.n)
    groups = feature_groups(names)

    configs = []
    for easy_kt in args.easy_kt:
        for hard_mcsp in args.hard_mcsp:
            for hard_kt in args.hard_kt:
                easy, hard = target_sets(args.n, mcsp, comp_xor, easy_kt, hard_mcsp, hard_kt)
                if not hard:
                    continue
                configs.append((easy_kt, hard_mcsp, hard_kt, easy, hard))

    print("=" * 112)
    print("Metacomplexity frontier audit")
    print("=" * 112)
    print(f"n={args.n}, functions={num_funcs(args.n)}, configs={len(configs)}")
    print("columns: acc / density / margin / expression")
    print()

    aggregate = {name: [] for name in groups}
    for cfg_i, (easy_kt, hard_mcsp, hard_kt, easy, hard) in enumerate(configs, start=1):
        print("-" * 112)
        print(
            f"config {cfg_i}: easy_kt<={easy_kt}, hard_mcsp>={hard_mcsp}, "
            f"hard_kt>={hard_kt}, easy={len(easy)}, hard={len(hard)}"
        )
        for label in ("struct", "kt", "meta", "no_mcsp", "no_kt", "all"):
            best = evolve(
                names,
                features,
                easy,
                hard,
                groups[label],
                seed=args.seed + 1009 * cfg_i + len(label),
                population=args.population,
                generations=args.generations,
                verbose=False,
            )
            aggregate[label].append(best)
            print(
                f"  {label:<7} acc={best.accuracy:.3f} "
                f"density={best.density:.3f} margin={best.margin:.3f}  "
                f"{describe(best, names)}"
            )

    print()
    print("=" * 112)
    print("Aggregate reading")
    print("=" * 112)
    for label in ("struct", "kt", "meta", "no_mcsp", "no_kt", "all"):
        vals = aggregate[label]
        if not vals:
            continue
        perfect = sum(1 for b in vals if b.accuracy == 1.0)
        mean_density = sum(b.density for b in vals) / len(vals)
        min_density = min(b.density for b in vals)
        mean_margin = sum(b.margin for b in vals) / len(vals)
        print(
            f"{label:<7} perfect={perfect:>2}/{len(vals)} "
            f"mean_density={mean_density:.3f} min_density={min_density:.3f} "
            f"mean_margin={mean_margin:.3f}"
        )

    print()
    print("Interpretation:")
    print("  structural/local success at high density = natural-proof warning.")
    print("  sparse success that needs MCSP/K^t = metacomplexity frontier signal.")
    print("  if no_mcsp stays strong, K^t-like features carry the signal without exact MCSP.")
    print("  if no_kt stays strong, exact MCSP is doing most of the work.")

    if args.holdout_trials:
        holdout_audit(args, names, features, mcsp, comp_xor, groups)


def signed_scores(best, features):
    raw = [
        sum(w * x for w, x in zip(best.weights, row))
        for row in features
    ]
    return [best.polarity * s for s in raw], best.polarity * best.threshold


def evaluate_fixed(best, features, easy, hard):
    scores, threshold = signed_scores(best, features)
    total = len(easy) + len(hard)
    correct = 0
    for m in easy:
        correct += scores[m] < threshold
    for m in hard:
        correct += scores[m] >= threshold
    hard_min = min(scores[m] for m in hard)
    easy_max = max(scores[m] for m in easy)
    density = sum(1 for s in scores if s >= threshold) / len(scores)
    return correct / total, hard_min - easy_max, density


def holdout_audit(args, names, features, mcsp, comp_xor, groups) -> None:
    easy, hard = target_sets(
        args.n,
        mcsp,
        comp_xor,
        args.holdout_easy_kt,
        args.holdout_hard_mcsp,
        args.holdout_hard_kt,
    )
    rng = random.Random(args.seed + 77)
    print()
    print("=" * 112)
    print("Holdout stability audit")
    print("=" * 112)
    print(
        f"target: easy_kt<={args.holdout_easy_kt}, "
        f"hard_mcsp>={args.holdout_hard_mcsp}, hard_kt>={args.holdout_hard_kt}; "
        f"easy={len(easy)}, hard={len(hard)}"
    )
    print(
        "Each trial trains on half of the easy/hard labels and tests on the held-out half. "
        "This exposes toy overfitting."
    )
    for label in ("struct", "meta", "all"):
        train_accs, test_accs, train_margins, test_margins, densities = [], [], [], [], []
        easy_list = sorted(easy)
        hard_list = sorted(hard)
        for trial in range(args.holdout_trials):
            rng.shuffle(easy_list)
            rng.shuffle(hard_list)
            easy_cut = max(1, len(easy_list) // 2)
            hard_cut = max(1, len(hard_list) // 2)
            train_easy = set(easy_list[:easy_cut])
            test_easy = set(easy_list[easy_cut:])
            train_hard = set(hard_list[:hard_cut])
            test_hard = set(hard_list[hard_cut:])
            if not test_easy or not test_hard:
                continue
            best = evolve(
                names,
                features,
                train_easy,
                train_hard,
                groups[label],
                seed=args.seed + 5000 + trial * 37 + len(label),
                population=args.population,
                generations=max(8, args.generations // 2),
                verbose=False,
            )
            tr_acc, tr_margin, density = evaluate_fixed(best, features, train_easy, train_hard)
            te_acc, te_margin, _ = evaluate_fixed(best, features, test_easy, test_hard)
            train_accs.append(tr_acc)
            test_accs.append(te_acc)
            train_margins.append(tr_margin)
            test_margins.append(te_margin)
            densities.append(density)
        if test_accs:
            print(
                f"  {label:<6} train_acc={sum(train_accs)/len(train_accs):.3f} "
                f"test_acc={sum(test_accs)/len(test_accs):.3f} "
                f"train_margin={sum(train_margins)/len(train_margins):.3f} "
                f"test_margin={sum(test_margins)/len(test_margins):.3f} "
                f"density={sum(densities)/len(densities):.3f}"
            )


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=3)
    parser.add_argument("--population", type=int, default=35)
    parser.add_argument("--generations", type=int, default=18)
    parser.add_argument("--seed", type=int, default=20260528)
    parser.add_argument("--easy-kt", type=int, nargs="+", default=[4, 5])
    parser.add_argument("--hard-mcsp", type=int, nargs="+", default=[7, 8, 9])
    parser.add_argument("--hard-kt", type=int, nargs="+", default=[6, 7, 8])
    parser.add_argument("--holdout-trials", type=int, default=8)
    parser.add_argument("--holdout-easy-kt", type=int, default=5)
    parser.add_argument("--holdout-hard-mcsp", type=int, default=8)
    parser.add_argument("--holdout-hard-kt", type=int, default=7)
    return parser.parse_args()


if __name__ == "__main__":
    run(parse_args())
