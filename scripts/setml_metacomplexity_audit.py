#!/usr/bin/env python3
"""Set-multilinear ↔ metacomplexity audit bridge (diagnostic).

This is the *meta-audit* bridge, not a proof bridge:
  1) Compute set-multilinear PD-matrix rank on a small family suite.
  2) Map each polynomial instance to a Boolean feature encoding.
  3) Define predicate P: "rank is high" over the finite instance index space.
  4) Compute exact formula complexity of P with metacomplexity.min_formula_size.

Interpretation:
- If P is very easy and reasonably large/useful, that is natural-property risk.
- If P is tiny/non-large or requires richer semantics, it is less obviously natural.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

from metacomplexity import min_formula_size
from setmultilinear_rank import (
    balanced_split,
    set_ml_pd_rank,
    spdp_rank,
    single_product,
    sum_of_products,
    imm,
    nw_setml,
)


@dataclass
class Instance:
    name: str
    builder: Callable[[], tuple]


def instance_suite() -> list[Instance]:
    # Exactly 8 instances -> 3-bit index space, so MCSP is exact and cheap.
    return [
        Instance("prod_d4_m3", lambda: single_product(4, 3)),
        Instance("sum2_d4_m3", lambda: sum_of_products(4, 3, 2)),
        Instance("sum3_d4_m3", lambda: sum_of_products(4, 3, 3)),
        Instance("sum5_d4_m3", lambda: sum_of_products(4, 3, 5)),
        Instance("imm_4_2", lambda: imm(4, 2)),
        Instance("imm_4_3", lambda: imm(4, 3)),
        Instance("imm_6_2", lambda: imm(6, 2)),
        Instance("nw_4_3_2", lambda: nw_setml(4, 3, 2)),
    ]


def bool_features(rank: int, nr: int, nc: int, gamma10: int, nvars: int) -> dict[str, int]:
    rel = rank / min(nr, nc)
    return {
        "rank_ge_3": int(rank >= 3),
        "rank_ge_5": int(rank >= 5),
        "rank_full": int(rel == 1.0),
        "gamma10_ge_20": int(gamma10 >= 20),
        "matrix_min_dim_ge_9": int(min(nr, nc) >= 9),
        "nvars_ge_20": int(nvars >= 20),
    }


def truth_mask(bits: list[int]) -> int:
    m = 0
    for i, b in enumerate(bits):
        if b:
            m |= 1 << i
    return m


def main() -> None:
    suite = instance_suite()

    rows = []
    high_rank_bits = []
    high_threshold = 3  # audit predicate P: rank >= 3

    print("=" * 96)
    print("SET-ML → META AUDIT BRIDGE (finite diagnostic)")
    print("=" * 96)
    print(f"instance count: {len(suite)} (index bits = 3)\n")

    for i, inst in enumerate(suite):
        f, buckets, all_vars = inst.builder()
        r, nr, nc = set_ml_pd_rank(f, buckets, balanced_split(len(buckets)), all_vars)
        g10 = int(spdp_rank(f, all_vars, 1, 0))
        feats = bool_features(r, nr, nc, g10, len(all_vars))
        high = int(r >= high_threshold)
        high_rank_bits.append(high)
        rows.append((i, inst.name, r, nr, nc, g10, feats, high))

    for i, name, r, nr, nc, g10, feats, high in rows:
        print(
            f"[{i}] {name:<12} rank={r:>3} matrix={nr:>3}x{nc:<3} "
            f"Gamma10={g10:>4} high(rank>={high_threshold})={high}"
        )
        print(f"     features={feats}")

    # P over 3-bit instance index space (8 points)
    P_mask = truth_mask(high_rank_bits)
    mcsp3 = min_formula_size(3)
    P_formula_gates = mcsp3[P_mask]

    positives = sum(high_rank_bits)
    density = positives / len(high_rank_bits)

    print("\n" + "-" * 96)
    print("Predicate P(index): 'set-ml rank is high' on this finite suite")
    print("-" * 96)
    print(f"P truth bits (index 0..7): {high_rank_bits}")
    print(f"P truth mask integer      : {P_mask}")
    print(f"exact formula complexity  : {P_formula_gates} gates (over 3-bit index)")
    print(f"density (largeness proxy) : {positives}/{len(high_rank_bits)} = {density:.3f}")

    print("\nAudit readout")
    if P_formula_gates <= 2 and density >= 0.25:
        print("- P is very easy + nontrivial density on this suite: naturalness risk signal.")
    elif P_formula_gates <= 4:
        print("- P is moderately easy on this tiny suite; treat as preliminary naturalness signal.")
    else:
        print("- P is not trivially easy on this tiny suite; no immediate naturalness alarm here.")
    print("- This is a finite diagnostic audit layer, not a lower-bound proof.")


if __name__ == "__main__":
    main()
