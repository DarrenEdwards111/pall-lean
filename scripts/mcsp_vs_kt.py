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
from kt_complexity import run_machine


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

    def kt(mask):
        return ktab.get(tt_string(mask, L), L)   # fall back to literal (= L tokens)

    mcsp_vals = [mcsp[m] for m in range(total)]
    kt_vals = [kt(m) for m in range(total)]
    r = pearson(mcsp_vals, kt_vals)

    print(f"\n   Pearson correlation  r(MCSP, K^t) = {r:+.3f}   "
          f"(positive => they loosely track)")

    # trend: average K^t within each MCSP bucket
    buckets = {}
    for m in range(total):
        buckets.setdefault(mcsp[m], []).append(kt(m))
    print("\n   trend  (MCSP value -> mean K^t over functions with that MCSP):")
    for k in sorted(buckets):
        vs = buckets[k]
        print(f"     MCSP={k:>2}:  mean K^t = {mean(vs):.2f}   (n={len(vs)})")

    # how many truth tables are compressible (K^t < literal) at all
    compressible = sum(1 for m in range(total) if kt(m) < L)
    print(f"\n   compressible truth tables (K^t < literal {L}): "
          f"{compressible}/{total}  (rest are literal-incompressible under U)")

    # named examples: agreement AND divergence
    print("\n   named functions  (MCSP = compute-cost,  K^t = describe-cost):")
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
            flag = "   <-- DIVERGES: easy to compute, NOT compressible under U"
        if mcsp[m] >= 8 and kt(m) >= L:
            flag = "   <-- high in BOTH"
        print(f"     {label:<18} MCSP = {mcsp[m]:>2},  K^t = {kt(m):>2}, "
              f"tt = {tt_string(m, L)}{flag}")

    print()
    print("-" * 92)
    print("READING THE RESULT (honest):")
    print(f"  * They LOOSELY track: r = {r:+.3f} > 0, and mean K^t rises with MCSP --")
    print("    a shared 'structure' core (simple functions tend to be cheap in both).")
    print("    BUT honestly WHY: the only sub-ceiling K^t values come from the 16")
    print("    compressible (periodic) truth tables, all at MCSP 0-2; everything with")
    print("    MCSP>=3 is pinned at K^t=8.  So r is driven by that low corner + the")
    print("    saturation ceiling, NOT a smooth gradient -- U is just too weak to")
    print("    compress most truth tables.")
    print("  * But they DIVERGE, and the divergences are the point:")
    print("      - AND/OR have LOW MCSP (easy to compute) yet HIGH K^t here: their")
    print("        truth tables ('00000001','01111111') are not PERIODIC, and U's only")
    print("        compression primitive is the counting loop -- so U cannot describe")
    print("        them short.  COMPUTE-cost and DESCRIBE-cost are genuinely different.")
    print("      - this is also MODEL-dependence of K^t: a richer machine (substitution/")
    print("        recursion) would compress more truth tables (e.g. parity's Thue-Morse")
    print("        pattern), changing K^t while MCSP stays fixed.")
    print("  * Takeaway: K^t-compressibility is (here) SUFFICIENT-ish for low MCSP but")
    print("    NOT necessary -- the measures share a core but capture different structure.")
    print("    MCSP is essentially 'circuit-flavoured K^t'; generic K^t is a different cut.")
    print("    That gap (Kt vs MCSP) is itself a real object of metacomplexity research.")


if __name__ == "__main__":
    run()
