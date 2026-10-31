#!/usr/bin/env python3
"""Demonstrate: the compiled-tableau SPDP rank blows up past n^200 for a TRIVIAL machine.
Mechanism (from GodMoveReal): rank >= C(n/3, log2 n), a MONOMIAL COUNT of the compilation
grid, independent of the machine's function. So a 4-step do-nothing DTM has the same blow-up
=> the measure does not separate P from NP."""
import math, itertools, random

# ---------- Part 1: the mechanism at computable scale ----------
# The blocked SPDP rank of a set-multilinear polynomial = rank of its flattening matrix
# (rows = kappa-subsets, cols = ell-subsets, entry = coeff of the union monomial).
# For a full-support (generic) set-multilinear poly this rank = C(m, kappa) -- a binomial.
# The compiled tableau polynomial has exactly this full-support monomial structure.

def gf2_rank(rows):
    rows = [set(r) for r in rows]  # each row = set of column indices with a 1
    basis = []
    for r in rows:
        for b in basis:
            piv = min(b)
            if piv in r:
                r ^= b
        if r:
            basis.append(r)
    return len(basis)

def flattening_rank(m, kappa, ell, seed=0):
    """SPDP flattening rank of a random full-support set-multilinear poly on m vars, deg kappa+ell."""
    random.seed(seed)
    kset = list(itertools.combinations(range(m), kappa))
    lset = list(itertools.combinations(range(m), ell))
    lindex = {s: j for j, s in enumerate(lset)}
    # random coefficient per degree-(kappa+ell) multilinear monomial
    coeff = {}
    for S in itertools.combinations(range(m), kappa + ell):
        coeff[S] = random.randint(0, 1)
    rows = []
    for A in kset:
        row = set()
        for B in lset:
            if set(A) & set(B): continue          # must be disjoint (set-multilinear)
            U = tuple(sorted(set(A) | set(B)))
            if coeff.get(U, 0):
                row.add(lindex[B])
        rows.append(row)
    return gf2_rank(rows)

print("=== Part 1: SPDP flattening rank of a compiled-tableau-like polynomial = binomial C(m,kappa) ===")
print(f"{'m':>3} {'kappa':>5} {'ell':>3} | {'computed rank':>13} | {'min binomial':>12}")
for (m, k, l) in [(4,2,1),(5,2,2),(6,2,2),(6,3,2),(7,3,2),(8,3,3)]:
    r = flattening_rank(m, k, l, seed=1)
    mn=min(math.comb(m,k),math.comb(m,l)); print(f"{m:>3} {k:>5} {l:>3} | {r:>13} | {mn:>10}   {'(= min binom, full)' if r==mn else '(binomial-scale)'}")
print("  -> the rank tracks the BINOMIAL monomial count min(C(m,k),C(m,l)); it counts grid monomials,\n     not machine behaviour. The NP-side theorem lower-bounds it by C(n/3, log2 n).\n")

# ---------- Part 2: the blow-up for a TRIVIAL 4-step machine ----------
# GodMoveReal.compiledPoly_rank_gt_npow200_at_large_n: for ANY DTM with timeBound<=4, numStates<=n,
#   rank >= C(floor(n/3), floor(log2 n)).  We take M = the do-nothing 4-step DTM.
def log2_binom(a, b):
    if b < 0 or b > a: return float('-inf')
    # sum of log2((a-i)/(i+1)); math.log2 handles arbitrary-precision ints exactly, no cancellation
    return sum(math.log2(a - i) - math.log2(i + 1) for i in range(b))

print("=== Part 2: trivial 4-step DTM (computes nothing) -- rank floor C(n/3, log2 n) vs n^200 ===")
print(f"  n = 2^t.   rank_floor = C(floor(n/3), floor(log2 n)).   threshold = n^200.")
print(f"{'t=log2 n':>9} | {'log2(rank_floor)':>16} | {'log2(n^200)=200t':>16} | {'verdict':>18}")
for t in [10, 50, 100, 200, 300, 400, 804]:
    n = 1 << t
    lo = log2_binom(n//3, t)              # log2 of the rank floor
    thr = 200 * t                         # log2(n^200)
    verdict = "rank >> n^200" if lo > thr else ("rank < n^200 (small n)" if lo < thr else "crossover")
    print(f"{t:>9} | {lo:>16.1f} | {thr:>16} | {verdict:>18}")

# crossover: log2(C(n/3,t)) ~ t*log2(n/3) - log2(t!) ~ t*(t-1.6) - (t log t - t) ~ t^2  vs 200 t
tc = 200
print(f"\n  Crossover ~ t = {tc}  (log2(rank) ~ t^2 overtakes 200t when t > 200, i.e. n > 2^200).")
print(f"  The theorem uses n >= 2^804: at t=804, log2(rank_floor) ~ {log2_binom((1<<804)//3,804):.0f}"
      f" vs 200t = {200*804} -> rank is ~2^{log2_binom((1<<804)//3,804):.0f}, threshold ~2^{200*804}.")
print("\n=== Conclusion ===")
print("  The rank floor C(n/3, log2 n) is SUPER-POLYNOMIAL (log2 ~ (log n)^2 = omega(log n)) and")
print("  blows past n^200 -- for the DO-NOTHING 4-step machine, identical to any hard machine.")
print("  => mlBlockedSpdpRank(compiledPoly) is a MONOMIAL-COUNT artifact of the compilation grid,")
print("     NOT a hardness certificate. It is high for EVERY DTM => it does NOT separate P from NP.")
print("     Hence the P-side upper bound (rank <= n^200) is FALSE. CookLevinFrontierHyp refuted.")
