"""
MCSP  vs  K^t  on the SAME functions  --  do the two metacomplexity measures track?

Two different "metacomplexity" measures of one Boolean function f : {0,1}^n -> {0,1}:

  MCSP(f)        = minimum formula gate-count to COMPUTE f          (from metacomplexity.py)
  K^t( tt(f) )   = time-bounded Kolmogorov complexity of f's        (from kt_complexity.py)
                   2^n-bit TRUTH TABLE -- the cost to DESCRIBE it.

These are NOT the same thing: one is compute-cost, the other is describe-cost.  We
compute BOTH for all 256 functions on n=3 (8-bit truth tables) and ask whether they
track each other.

K^t here is computed by ACTUAL program enumeration on the fixed machine U of
kt_complexity.py (up to a token budget; longer strings fall back to the literal,
which is an honest upper bound since K^t is a min).  NOTE: U's only compression
primitive is the counting loop, so U captures PERIODIC structure only -- it cannot
compress, e.g., the Thue-Morse pattern.  We flag where that model-weakness matters.
"""
from __future__ import annotations
from itertools import product as iproduct
from statistics import mean

from metacomplexity import (min_formula_size, num_funcs, var_mask, NOT,
                            f_and, f_or, f_maj, f_xor)
from kt_complexity import compositional_kt_upper_bounds, run_machine


# ----------------------------------------------------------------------------
# Enumerate K^t for every 8-bit string reachable with <= max_tokens tokens.
# ----------------------------------------------------------------------------
TOKENS = [("E0",), ("E1",), ("I",), ("H",),
          ("J", -1), ("J", -2), ("J", -3), ("J", -4)]


def enumerate_kt(out_len, max_tokens, t):
    """dict: 8-bit-output-string -> min #tokens of a program that halts with that
    output within t steps.  Strings needing more than max_tokens are absent
    (caller falls back to the literal length = out_len)."""
    best = {}
    for length in range(1, max_tokens + 1):
        for prog in iproduct(TOKENS, repeat=length):
            out, halted, _ = run_machine(list(prog), t=t, Lmax=out_len)
            if halted and len(out) == out_len:
                if out not in best or length < best[out]:
                    best[out] = length
    return best


def tt_string(mask, L):
    """Truth-table mask -> its L-bit string (bit i = f(input i))."""
    return "".join("1" if (mask >> i) & 1 else "0" for i in range(L))


def pearson(xs, ys):
    mx, my = mean(xs), mean(ys)
    num = sum((a - mx) * (b - my) for a, b in zip(xs, ys))
    dx = sum((a - mx) ** 2 for a in xs) ** 0.5
    dy = sum((b - my) ** 2 for b in ys) ** 0.5
    return num / (dx * dy) if dx and dy else 0.0


def run():
    n = 3
    L = 1 << n                      # 8-bit truth tables
    total = num_funcs(n)            # 256

    print("=" * 92)
    print(f"MCSP vs K^t  on all {total} functions of n={n}  (8-bit truth tables)")
    print("=" * 92)
    print("   computing MCSP (formula gate-count) ...")
    mcsp = min_formula_size(n)
    print("   computing K^t by program enumeration on U (token budget 6) ...")
    ktab = enumerate_kt(out_len=L, max_tokens=6, t=48)
    print("   computing compositional K^t upper bounds (Boolean basis, cost <= 8) ...")
    comp_bool = compositional_kt_upper_bounds(n, max_cost=L, include_xor=False)
    print("   computing compositional K^t upper bounds (Boolean basis + XOR, cost <= 8) ...")
    comp_xor = compositional_kt_upper_bounds(n, max_cost=L, include_xor=True)

    def kt(mask):
        return ktab.get(tt_string(mask, L), L)   # fall back to literal (= L tokens)

    def kt_comp_bool(mask):
        return min(comp_bool.get(mask, L), L)

    def kt_comp_xor(mask):
        return min(comp_xor.get(mask, L), L)

    mcsp_vals = [mcsp[m] for m in range(total)]
    kt_vals = [kt(m) for m in range(total)]
    kt_bool_vals = [kt_comp_bool(m) for m in range(total)]
    kt_xor_vals = [kt_comp_xor(m) for m in range(total)]
    r = pearson(mcsp_vals, kt_vals)
    r_bool = pearson(mcsp_vals, kt_bool_vals)
    r_xor = pearson(mcsp_vals, kt_xor_vals)

    print("\n   Pearson correlations with MCSP:")
    print(f"     tape U K^t                  r = {r:+.3f}")
    print(f"     compositional K^t           r = {r_bool:+.3f}")
    print(f"     compositional K^t + XOR     r = {r_xor:+.3f}")
    print("   (positive => they loosely track; changes show model dependence)")

    # trend: average K^t within each MCSP bucket
    buckets = {}
    for m in range(total):
        buckets.setdefault(mcsp[m], []).append(kt(m))
    print("\n   trend  (MCSP value -> mean K^t over functions with that MCSP):")
    for k in sorted(buckets):
        vs = buckets[k]
        print(f"     MCSP={k:>2}:  mean K^t = {mean(vs):.2f}   (n={len(vs)})")
    print("\n   richer-machine trend  (MCSP -> mean compositional K^t / +XOR K^t):")
    for k in sorted(buckets):
        masks = [m for m in range(total) if mcsp[m] == k]
        print(f"     MCSP={k:>2}:  comp = {mean(kt_comp_bool(m) for m in masks):.2f}, "
              f"comp+XOR = {mean(kt_comp_xor(m) for m in masks):.2f}   (n={len(masks)})")

    # how many truth tables are compressible (K^t < literal) at all
    compressible = sum(1 for m in range(total) if kt(m) < L)
    compressible_bool = sum(1 for m in range(total) if kt_comp_bool(m) < L)
    compressible_xor = sum(1 for m in range(total) if kt_comp_xor(m) < L)
    print(f"\n   compressible truth tables (K^t < literal {L}): "
          f"{compressible}/{total}  (rest are literal-incompressible under U)")
    print(f"   compositional-compressible truth tables:")
    print(f"     Boolean basis      : {compressible_bool}/{total}")
    print(f"     Boolean basis + XOR: {compressible_xor}/{total}")

    # named examples: agreement AND divergence
    print("\n   named functions  (MCSP = compute-cost, K^t variants = describe-cost):")
    named = [
        ("const 0", 0),
        ("x0 (projection)", var_mask(n, 0)),
        ("NOT x0", NOT(var_mask(n, 0), n)),
        ("AND(x0,x1,x2)", f_and(n)),
        ("OR(x0,x1,x2)", f_or(n)),
        ("majority", f_maj(n)),
        ("parity (XOR)", f_xor(n)),
    ]
    for label, m in named:
        flag = ""
        if mcsp[m] <= 2 and kt(m) >= L:
            flag = "   <-- U-divergence: easy to compute, not periodic-compressible"
        if label.startswith("parity"):
            flag = "   <-- XOR primitive flips the K^t reading"
        print(f"     {label:<18} MCSP = {mcsp[m]:>2}, "
              f"U = {kt(m):>2}, comp = {kt_comp_bool(m):>2}, "
              f"comp+XOR = {kt_comp_xor(m):>2}, "
              f"tt = {tt_string(m, L)}{flag}")

    print()
    print("-" * 92)
    print("READING THE RESULT (honest):")
    print(f"  * The weak tape machine has r = {r:+.3f}; the richer compositional machines")
    print(f"    have r = {r_bool:+.3f} and r = {r_xor:+.3f}.  The shift is the point:")
    print("    K^t is machine-relative up to an invariance constant, and at this tiny")
    print("    scale the primitive set visibly matters.")
    print("  * AND/OR were false negatives for the tape U: they are easy to compute but")
    print("    non-periodic as 8-bit strings.  Adding substitution/composition compresses")
    print("    them immediately.")
    print("  * Parity is the sharper diagnostic: it stays literal-size in the Boolean")
    print("    compositional model but drops when XOR is admitted as a primitive.  That")
    print("    is exactly the metacomplexity lesson: the observer machine's instruction")
    print("    set changes which structure is visible under a fixed time/description cap.")
    print("  * Takeaway: K^t-compressibility is (here) SUFFICIENT-ish for low MCSP but")
    print("    NOT necessary -- the measures share a core but capture different structure.")
    print("    MCSP is essentially 'circuit-flavoured K^t'; generic K^t is a different cut.")
    print("    That gap (Kt vs MCSP) is itself a real object of metacomplexity research.")


if __name__ == "__main__":
    run()
