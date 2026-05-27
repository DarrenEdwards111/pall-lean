"""
Metacomplexity prototype  --  the "complexity of computing complexity" track.

This is the PARALLEL track to setmultilinear_rank.py.  Where the set-multilinear
measure is an ALGEBRAIC, object-level lower-bound tool, metacomplexity is the
META-level question: how hard is a function to DESCRIBE / compress, and how hard
is it to COMPUTE that hardness?  It is the home of MCSP (Minimum Circuit Size
Problem) and K^t (time-bounded Kolmogorov complexity).

Concrete measure implemented here (exact, computable for small n):
    mcsp(f) := minimum number of 2-input {AND, OR} / 1-input {NOT} gates in a
               FORMULA computing the Boolean function f : {0,1}^n -> {0,1},
               with variables and constants free at the leaves.
    (Formula = tree; this is the formula-complexity cousin of true circuit-size
     MCSP, which allows DAG sharing.  Formula gate-count over-estimates circuit
     size but is well-defined, monotone, and exactly computable by Dijkstra over
     the 2^(2^n) function space.  We compute it for ALL functions on n=2,3.)

This MEASURES and MAPS.  It validates the measure on known functions, exhibits
the metacomplexity separation (structured functions compress; most functions do
not), and then states -- honestly -- where the metacomplexity "bridge" to P vs NP
goes, and the genuine relationship to the set-multilinear (algebraic) track.

WHY THIS RESONATES WITH THE N-FRAME BOOK (honest resonance, not a proof):
  * K^t is description length UNDER A TIME BUDGET -- literally the book's
    "computational time budget" lens on an object.
  * MCSP / Kolmogorov complexity is the OBSERVER's shortest description of a
    function: a compression / observer-relative measure.
  * the hardness of MCSP is bound up with SELF-REFERENCE (recursion theorem),
    the book's Goedel-Penrose tower theme.
These are real conceptual bridges to the framework.  They are NOT a proof bridge
to P vs NP, for the reason mapped at the end (metacomplexity is exactly where the
natural-proofs barrier LIVES).
"""
from __future__ import annotations
import heapq
from itertools import product


# ----------------------------------------------------------------------------
# Boolean functions on n bits as truth tables packed into an int bitmask.
# Bit i of the mask = f(input i), where input i is the n-bit number i.
# ----------------------------------------------------------------------------
def num_funcs(n):
    return 1 << (1 << n)            # 2^(2^n)


def full_mask(n):
    return (1 << (1 << n)) - 1


def var_mask(n, j):
    """Truth table of the projection x_j (j-th input bit)."""
    m = 0
    for i in range(1 << n):
        if (i >> j) & 1:
            m |= (1 << i)
    return m


def NOT(m, n):
    return (~m) & full_mask(n)


def AND(a, b):
    return a & b


def OR(a, b):
    return a | b


def min_formula_size(n):
    """Exact minimum formula gate-count for EVERY function on n bits.

    Dijkstra over the function space: leaves (constants + projections) cost 0;
    relaxations are NOT (1 gate) and AND/OR (1 gate) over already-finalized
    functions.  Returns dict {truth_table_mask: min_gates}.
    """
    N = num_funcs(n)
    fmask = full_mask(n)
    INF = float("inf")
    cost = {m: INF for m in range(N)}

    leaves = [0, fmask] + [var_mask(n, j) for j in range(n)]   # consts + vars
    pq = []
    for m in leaves:
        if cost[m] > 0:
            cost[m] = 0
            heapq.heappush(pq, (0, m))

    finalized = []
    done = [False] * N
    while pq:
        c, m = heapq.heappop(pq)
        if done[m]:
            continue
        done[m] = True
        finalized.append(m)

        def relax(nm, nc):
            if nc < cost[nm]:
                cost[nm] = nc
                heapq.heappush(pq, (nc, nm))

        relax(NOT(m, n), c + 1)
        for g in finalized:
            cg = cost[g]
            relax(AND(m, g), c + cg + 1)
            relax(OR(m, g), c + cg + 1)
    return cost


# ----------------------------------------------------------------------------
# Named functions for validation
# ----------------------------------------------------------------------------
def from_predicate(n, pred):
    m = 0
    for i in range(1 << n):
        bits = [(i >> j) & 1 for j in range(n)]
        if pred(bits):
            m |= (1 << i)
    return m


def f_and(n):     return from_predicate(n, lambda b: all(b))
def f_or(n):      return from_predicate(n, lambda b: any(b))
def f_xor(n):     return from_predicate(n, lambda b: sum(b) % 2 == 1)
def f_maj(n):     return from_predicate(n, lambda b: sum(b) > n / 2)
def f_const0(n):  return 0
def f_thr2(n):    return from_predicate(n, lambda b: sum(b) >= 2)


# ----------------------------------------------------------------------------
# Report
# ----------------------------------------------------------------------------
def run():
    print("=" * 90)
    print("VALIDATION  --  n=2: minimum formula gate-count over {AND,OR,NOT}, all 16 functions")
    print("=" * 90)
    n = 2
    cost = min_formula_size(n)
    checks = {
        "const 0": (f_const0(n), 0),
        "x0": (var_mask(n, 0), 0),
        "AND(x0,x1)": (f_and(n), 1),
        "OR(x0,x1)": (f_or(n), 1),
        "NOT x0": (NOT(var_mask(n, 0), n), 1),
    }
    ok = True
    for name, (m, expected) in checks.items():
        got = cost[m]
        good = (got == expected)
        ok = ok and good
        print(f"   {name:<14} min-gates = {got}   (expected {expected})  "
              f"[{'OK' if good else 'MISMATCH'}]")
    print(f"   XOR(x0,x1)     min-gates = {cost[f_xor(n)]}   "
          f"(hardest 2-bit function class)")
    by_cost = {}
    for m, c in cost.items():
        by_cost.setdefault(c, 0)
        by_cost[c] += 1
    print("   distribution over all 16 functions (gates -> count):",
          {k: by_cost[k] for k in sorted(by_cost)})
    print(f"\n   implementation check: {'PASSED' if ok else 'FAILED'}\n")

    print("=" * 90)
    print("METACOMPLEXITY SEPARATION  --  n=3: structured functions compress, parity does not")
    print("   (structured -> low MCSP;  parity -> high MCSP;  Shannon hardness is asymptotic)")
    print("=" * 90)
    n = 3
    cost = min_formula_size(n)
    named = [
        ("const 0", f_const0(n)),
        ("AND(x0,x1,x2)", f_and(n)),
        ("OR(x0,x1,x2)", f_or(n)),
        ("threshold >=2", f_thr2(n)),
        ("majority", f_maj(n)),
        ("parity (XOR)", f_xor(n)),
    ]
    for name, m in named:
        print(f"   {name:<18} mcsp = {cost[m]:>2} gates")
    by_cost = {}
    for m, c in cost.items():
        by_cost.setdefault(c, 0)
        by_cost[c] += 1
    maxc = max(by_cost)
    total = num_funcs(n)
    hard = sum(v for k, v in by_cost.items() if k >= maxc - 1)
    print(f"\n   full distribution over all {total} functions (gates -> count):")
    print("     ", {k: by_cost[k] for k in sorted(by_cost)})
    mid = sum(v for k, v in by_cost.items() if 5 <= k <= 6)
    cheap = sum(v for k, v in by_cost.items() if k <= 4)
    print(f"   max MCSP = {maxc} gates;  cheap (<=4): {cheap}/{total}, "
          f"mid (5-6): {mid}/{total}, top (>=max-1): {hard}/{total}.")
    print("   => the SEPARATION that IS visible at n=3: structured functions")
    print("      (AND/OR/threshold/majority) are cheap (<=4); parity is hardest (11).")
    print("   HONEST CAVEAT: the Shannon/Lupanov fact 'almost ALL functions are")
    print("      near-maximal' is ASYMPTOTIC (n -> infinity); at n=3 the bulk sits")
    print("      mid-range (5-6 gates), not at the max -- same small-instance caveat")
    print("      as super-polynomial gaps.  The measure is exact and correct; the")
    print("      'most functions are hard' phenomenon just is not pronounced yet here.")

    print()
    print("=" * 90)
    print("THE BRIDGE MAP  --  where metacomplexity goes, honestly")
    print("=" * 90)
    print("""   A metacomplexity 'bridge' to P vs NP would need:
       SAT in P  ==>  (something about MCSP / K^t collapses)  ==>  contradiction.

   What is PROVEN (real, but not worst-case P!=NP):
     * MCSP easy  ==>  no one-way functions  (cryptographic / Razborov-Rudich).
     * worst-case <-> average-case links for MCSP/K^t (Hirahara and others).
   What is OPEN (the live frontier):
     * MCSP's own complexity (not known NP-complete, not known in P).
     * a worst-case separation FROM metacomplexity.

   THE WALL (why this is not a free bridge):
     Razborov-Rudich 'natural proofs' IS a metacomplexity statement: a natural
     proof is an EFFICIENT, LARGE distinguisher of high-MCSP from low-MCSP
     functions.  So metacomplexity is exactly WHERE THE BARRIER LIVES.  Any
     separation built from it must be NON-natural -- it must NOT yield such an
     efficient distinguisher.  Same wall, viewed from the inside.

   THE GENUINE PARALLEL TRACK (your 'combine or parallel' question, answered):
     metacomplexity (Boolean)  ||  ALGEBRAIC NATURAL PROOFS (algebraic)
     The algebraic analogue (Forbes-Shpilka-Volk; Grochow-Kumar-Saks-Saraf) asks:
     is there an efficient low-degree certificate of algebraic hardness?  The
     set-multilinear PD-rank measure IS a candidate 'algebraic natural property'.
     So the two tracks do NOT merge into one number -- instead, the metacomplexity
     track AUDITS the set-multilinear track: it tells you whether a rank measure
     is barrier-limited (natural) or could escape.  That is the real, productive
     relationship -- a meta-track checking the object-track, not a combined measure.
""")


if __name__ == "__main__":
    run()
