#!/usr/bin/env python3
"""
Evolutionary search for Boolean-function invariants.

This is a finite diagnostic for "what kind of invariant might separate
P-like functions from hard-looking functions?"  It does not prove P != NP.

We work on all Boolean functions on n=3 inputs.  The target split is deliberately
guarded:

* easy/P-like examples include functions that a reasonable observer model should
  not call hard, including parity when XOR is admitted as a primitive;
* hard-looking examples are functions with high exact formula-MCSP and no short
  compositional K^t(+XOR) description at this tiny scale.

The evolutionary algorithm searches integer linear combinations of feature
columns.  Two modes are reported:

* structural features only: sensitivity, ANF degree/sparsity, Fourier/Walsh,
  decision-tree depth, certificate complexity, monotonicity, junta size;
* metacomplexity features allowed: exact MCSP and compositional K^t.

If only the second mode separates cleanly, the search is telling us that the
candidate invariant is really metacomplexity, not a new simple local/rank-like
measure.
"""

from __future__ import annotations

import argparse
import math
import os
import random
from dataclasses import dataclass
from statistics import mean

from metacomplexity import (
    NOT,
    f_and,
    f_maj,
    f_or,
    f_xor,
    full_mask,
    min_formula_size,
    num_funcs,
    var_mask,
)
from kt_complexity import compositional_kt_upper_bounds


def bit(mask: int, i: int) -> int:
    return (mask >> i) & 1


def truth_bits(mask: int, n: int) -> list[int]:
    return [bit(mask, i) for i in range(1 << n)]


def popcount(x: int) -> int:
    return int(x.bit_count())


def anf_coefficients(mask: int, n: int) -> list[int]:
    coeffs = truth_bits(mask, n)
    # Mobius transform over GF(2), in-place.
    for j in range(n):
        step = 1 << j
        for base in range(1 << n):
            if base & step:
                coeffs[base] ^= coeffs[base ^ step]
    return coeffs


def algebraic_degree(mask: int, n: int) -> int:
    coeffs = anf_coefficients(mask, n)
    deg = 0
    for mon, c in enumerate(coeffs):
        if c:
            deg = max(deg, popcount(mon))
    return deg


def anf_sparsity(mask: int, n: int) -> int:
    return sum(anf_coefficients(mask, n))


def sensitivity_values(mask: int, n: int) -> list[int]:
    vals = []
    for x in range(1 << n):
        sx = 0
        fx = bit(mask, x)
        for j in range(n):
            if bit(mask, x ^ (1 << j)) != fx:
                sx += 1
        vals.append(sx)
    return vals


def decision_tree_depth(mask: int, n: int) -> int:
    from functools import lru_cache

    @lru_cache(None)
    def rec(fixed_zero: int, fixed_one: int) -> int:
        vals = []
        free = []
        for x in range(1 << n):
            if (x & fixed_zero) == 0 and (x & fixed_one) == fixed_one:
                vals.append(bit(mask, x))
        if not vals or all(v == vals[0] for v in vals):
            return 0
        for j in range(n):
            if not ((fixed_zero | fixed_one) >> j) & 1:
                free.append(j)
        return 1 + min(
            max(rec(fixed_zero | (1 << j), fixed_one),
                rec(fixed_zero, fixed_one | (1 << j)))
            for j in free
        )

    return rec(0, 0)


def certificate_complexity(mask: int, n: int) -> int:
    max_cert = 0
    variables = list(range(n))
    for x in range(1 << n):
        target = bit(mask, x)
        best = n + 1
        for subset_bits in range(1 << n):
            subset = [variables[j] for j in range(n) if (subset_bits >> j) & 1]
            ok = True
            for y in range(1 << n):
                if all(bit(x, j) == bit(y, j) for j in subset):
                    if bit(mask, y) != target:
                        ok = False
                        break
            if ok:
                best = min(best, len(subset))
        max_cert = max(max_cert, best)
    return max_cert


def walsh_spectrum(mask: int, n: int) -> list[int]:
    vals = [1 if bit(mask, x) == 0 else -1 for x in range(1 << n)]
    spec = []
    for s in range(1 << n):
        total = 0
        for x, v in enumerate(vals):
            total += v * (1 if popcount(s & x) % 2 == 0 else -1)
        spec.append(total)
    return spec


def junta_size(mask: int, n: int) -> int:
    deps = 0
    for j in range(n):
        if any(bit(mask, x) != bit(mask, x ^ (1 << j)) for x in range(1 << n)):
            deps += 1
    return deps


def monotone_violations(mask: int, n: int) -> int:
    bad = 0
    for x in range(1 << n):
        for j in range(n):
            y = x | (1 << j)
            if x != y and bit(mask, x) > bit(mask, y):
                bad += 1
    return bad


def named_easy_masks(n: int) -> set[int]:
    masks = {0, full_mask(n), f_and(n), f_or(n), f_maj(n), f_xor(n)}
    for j in range(n):
        v = var_mask(n, j)
        masks.add(v)
        masks.add(NOT(v, n))
    return masks


def feature_table(n: int):
    mcsp = min_formula_size(n)
    comp = compositional_kt_upper_bounds(n, max_cost=1 << n, include_xor=False)
    comp_xor = compositional_kt_upper_bounds(n, max_cost=1 << n, include_xor=True)
    total = num_funcs(n)
    rows = []
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
        "mcsp",
        "comp_kt",
        "comp_kt_xor",
    ]
    for m in range(total):
        sens = sensitivity_values(m, n)
        walsh = walsh_spectrum(m, n)
        weight = popcount(m)
        row = [
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
            mcsp[m],
            min(comp.get(m, 1 << n), 1 << n),
            min(comp_xor.get(m, 1 << n), 1 << n),
        ]
        rows.append(row)
    maxima = [max(abs(row[i]) for row in rows) or 1 for i in range(len(names))]
    norm = [[row[i] / maxima[i] for i in range(len(names))] for row in rows]
    return names, rows, norm, mcsp, comp_xor


@dataclass(frozen=True)
class Scored:
    fitness: float
    accuracy: float
    margin: float
    density: float
    threshold: float
    polarity: int
    weights: tuple[int, ...]


def best_threshold(scores: list[float], easy: set[int], hard: set[int]) -> tuple[float, float, float, float, int]:
    candidates = sorted(set(scores))
    thresholds = [candidates[0] - 1.0]
    thresholds += [(a + b) / 2 for a, b in zip(candidates, candidates[1:])]
    thresholds += [candidates[-1] + 1.0]

    best = (-1.0, -1.0, 0.0, thresholds[0], 1)
    total_labeled = len(easy) + len(hard)
    for polarity in (1, -1):
        pscores = [polarity * s for s in scores]
        for t in thresholds:
            pt = polarity * t
            correct = 0
            for m in easy:
                correct += pscores[m] < pt
            for m in hard:
                correct += pscores[m] >= pt
            acc = correct / total_labeled
            hard_min = min(pscores[m] for m in hard)
            easy_max = max(pscores[m] for m in easy)
            margin = hard_min - easy_max
            density = sum(1 for s in pscores if s >= pt) / len(pscores)
            objective = acc + 0.05 * margin - 0.10 * max(0.0, density - 0.40)
            if objective > best[0]:
                best = (objective, acc, margin, t, polarity)
    _, acc, margin, threshold, polarity = best
    pscores = [polarity * s for s in scores]
    density = sum(1 for s in pscores if s >= polarity * threshold) / len(scores)
    return acc, margin, density, threshold, polarity


def score_weights(weights: tuple[int, ...], features: list[list[float]], easy: set[int], hard: set[int]) -> Scored:
    raw = [
        sum(w * x for w, x in zip(weights, row))
        for row in features
    ]
    acc, margin, density, threshold, polarity = best_threshold(raw, easy, hard)
    l1 = sum(abs(w) for w in weights)
    sparsity_penalty = 0.002 * l1
    fitness = acc + 0.05 * margin - 0.10 * max(0.0, density - 0.40) - sparsity_penalty
    return Scored(fitness, acc, margin, density, threshold, polarity, weights)


def random_weights(k: int, rng: random.Random, width: int = 5) -> tuple[int, ...]:
    ws = []
    for _ in range(k):
        ws.append(rng.randint(-width, width) if rng.random() < 0.45 else 0)
    if all(w == 0 for w in ws):
        ws[rng.randrange(k)] = rng.choice([-1, 1])
    return tuple(ws)


def mutate(weights: tuple[int, ...], rng: random.Random, width: int = 8) -> tuple[int, ...]:
    ws = list(weights)
    for _ in range(rng.randint(1, 3)):
        i = rng.randrange(len(ws))
        ws[i] = max(-width, min(width, ws[i] + rng.choice([-2, -1, 1, 2])))
        if rng.random() < 0.15:
            ws[i] = 0
    if all(w == 0 for w in ws):
        ws[rng.randrange(len(ws))] = rng.choice([-1, 1])
    return tuple(ws)


def evolve(names, features, easy, hard, allowed, seed, population, generations, verbose=True) -> Scored:
    rng = random.Random(seed)
    subfeatures = [[row[i] for i in allowed] for row in features]
    pop = [random_weights(len(allowed), rng) for _ in range(population)]
    best = None
    for gen in range(generations + 1):
        scored = [score_weights(w, subfeatures, easy, hard) for w in pop]
        scored.sort(key=lambda s: s.fitness, reverse=True)
        if best is None or scored[0].fitness > best.fitness:
            best = scored[0]
        if verbose:
            print(
                f"gen {gen:02d}: fit={scored[0].fitness:.3f} "
                f"acc={scored[0].accuracy:.3f} margin={scored[0].margin:.3f} "
                f"density={scored[0].density:.3f}"
            )
        elites = scored[: max(2, population // 4)]
        pop = [e.weights for e in elites]
        while len(pop) < population:
            parent = rng.choice(elites).weights
            pop.append(mutate(parent, rng))
    assert best is not None
    # Lift weights back to full feature space for reporting.
    full = [0] * len(names)
    for local_i, feature_i in enumerate(allowed):
        full[feature_i] = best.weights[local_i]
    return Scored(best.fitness, best.accuracy, best.margin, best.density,
                  best.threshold, best.polarity, tuple(full))


def describe(best: Scored, names: list[str]) -> str:
    terms = []
    for name, w in zip(names, best.weights):
        if w:
            terms.append(f"{w:+d}*{name}")
    body = " ".join(terms) if terms else "0"
    polarity = "" if best.polarity == 1 else "-("
    close = "" if best.polarity == 1 else ")"
    return f"{polarity}{body}{close} >= {best.polarity * best.threshold:.3f}"


def invariant_scores(best: Scored, features: list[list[float]]) -> list[float]:
    raw = [
        sum(w * x for w, x in zip(best.weights, row))
        for row in features
    ]
    return [best.polarity * s for s in raw]


def plot_density(
    path: str,
    title: str,
    best: Scored,
    features: list[list[float]],
    easy: set[int],
    hard: set[int],
) -> None:
    os.environ.setdefault("MPLCONFIGDIR", "/tmp/matplotlib")
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    scores = invariant_scores(best, features)
    threshold = best.polarity * best.threshold
    ordered = sorted(scores)
    survival_x = ordered
    total = len(scores)
    survival_y = [(total - i) / total for i in range(total)]

    easy_scores = [scores[i] for i in sorted(easy)]
    hard_scores = [scores[i] for i in sorted(hard)]

    fig, (ax_hist, ax_density) = plt.subplots(2, 1, figsize=(9, 7), constrained_layout=True)
    ax_hist.hist(scores, bins=24, alpha=0.28, label="all functions", color="#808080")
    ax_hist.hist(easy_scores, bins=16, alpha=0.70, label="easy/P-like", color="#2f80ed")
    ax_hist.hist(hard_scores, bins=12, alpha=0.78, label="hard-looking", color="#d64545")
    ax_hist.axvline(threshold, color="#111111", linestyle="--", linewidth=1.4, label="threshold")
    ax_hist.set_title(title)
    ax_hist.set_ylabel("count")
    ax_hist.legend(loc="best")

    ax_density.plot(survival_x, survival_y, color="#111111", linewidth=1.8)
    ax_density.axvline(threshold, color="#111111", linestyle="--", linewidth=1.2)
    ax_density.axhline(best.density, color="#888888", linestyle=":", linewidth=1.2)
    ax_density.scatter([threshold], [best.density], color="#111111", zorder=3)
    ax_density.set_xlabel("signed invariant score")
    ax_density.set_ylabel("accepted density")
    ax_density.set_ylim(-0.02, 1.02)
    ax_density.text(
        0.02,
        0.08,
        f"density={best.density:.3f}\naccuracy={best.accuracy:.3f}\nmargin={best.margin:.3f}",
        transform=ax_density.transAxes,
        bbox={"facecolor": "white", "edgecolor": "#cccccc", "alpha": 0.9},
    )

    fig.savefig(path, dpi=160)
    plt.close(fig)


def run(args) -> None:
    names, _raw, features, mcsp, comp_xor = feature_table(args.n)
    easy = set(named_easy_masks(args.n))
    easy |= {m for m in range(num_funcs(args.n)) if comp_xor.get(m, 1 << args.n) <= args.easy_kt}
    hard = {
        m for m in range(num_funcs(args.n))
        if mcsp[m] >= args.hard_mcsp and comp_xor.get(m, 1 << args.n) >= args.hard_kt
    }
    hard -= easy

    structural = [i for i, name in enumerate(names) if name not in {"mcsp", "comp_kt", "comp_kt_xor"}]
    meta = list(range(len(names)))

    print("=" * 92)
    print("Boolean invariant evolutionary search")
    print("=" * 92)
    print(f"n={args.n}, functions={num_funcs(args.n)}")
    print(f"easy/P-like set size: {len(easy)}")
    print(f"hard-looking set size: {len(hard)}")
    print("easy guard includes named P-like functions and comp_kt_xor below threshold.")
    print("hard guard requires high exact MCSP and high comp_kt_xor.")

    for label, allowed in [
        ("structural/local features only", structural),
        ("metacomplexity features allowed", meta),
    ]:
        print("\n" + "-" * 92)
        print(label)
        print("-" * 92)
        best = evolve(names, features, easy, hard, allowed, args.seed,
                      args.population, args.generations, verbose=True)
        print("best invariant:")
        print("  " + describe(best, names))
        print(
            f"  accuracy={best.accuracy:.3f}, margin={best.margin:.3f}, "
            f"accept-density={best.density:.3f}, fitness={best.fitness:.3f}"
        )
        if label.startswith("metacomplexity") and any(
            names[i] in {"mcsp", "comp_kt", "comp_kt_xor"} and w
            for i, w in enumerate(best.weights)
        ):
            print("  readout: the search used metacomplexity directly.")
        elif best.density > 0.35 and best.accuracy > 0.95:
            print("  readout: high-density efficient-looking property; natural-proofs risk.")
        else:
            print("  readout: finite diagnostic only; no P-vs-NP bridge.")
        if args.plot_prefix:
            stem = label.replace("/", "_").replace(" ", "_")
            path = f"{args.plot_prefix}_{stem}.png"
            plot_density(path, label, best, features, easy, hard)
            print(f"  plot: {path}")


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=3)
    parser.add_argument("--population", type=int, default=40)
    parser.add_argument("--generations", type=int, default=30)
    parser.add_argument("--seed", type=int, default=20260528)
    parser.add_argument("--easy-kt", type=int, default=5)
    parser.add_argument("--hard-mcsp", type=int, default=8)
    parser.add_argument("--hard-kt", type=int, default=7)
    parser.add_argument(
        "--plot-prefix",
        default="",
        help="write density visualizations as <prefix>_<mode>.png",
    )
    return parser.parse_args()


if __name__ == "__main__":
    run(parse_args())
