#!/usr/bin/env python3
"""Build the composite mu's Layer 2 (hard-side witness = Tseitin/expander rigidity) and test it.
Result: the witness collapses -- Tseitin formulas are HARD for resolution (BSW expander width LB,
the repo's 'genuine asset') but EASY for P: they are GF(2) linear systems, solved by Gaussian
elimination in poly time. So the hard-side witness is high on a P-easy object => it is NOT an
NP-hardness witness, and no composite mu built on it can separate P from NP."""
import random

def three_regular_graph(nv, seed):
    """A random 3-regular (expander-ish) multigraph on nv vertices; return edge list."""
    random.seed(seed)
    stubs = [v for v in range(nv) for _ in range(3)]
    random.shuffle(stubs)
    edges = []
    for i in range(0, len(stubs) - 1, 2):
        a, b = stubs[i], stubs[i+1]
        edges.append((a, b))
    return edges

def gf2_solve(A, b):
    """Solve A x = b over GF(2). A: list of int bitmasks (rows over columns). b: list of {0,1}.
    Returns (solvable, x_bitmask, rank, steps)."""
    m = len(A); ncol = max((r.bit_length() for r in A), default=0)
    rows = [(A[i], b[i]) for i in range(m)]
    steps = 0
    pivots = []          # (col, row_index_in_reduced)
    reduced = []
    for (r, rb) in rows:
        cur, curb = r, rb
        for (pr, prb) in reduced:
            steps += 1
            piv = (pr & -pr)            # lowest set bit = pivot column
            if cur & piv:
                cur ^= pr; curb ^= prb
        if cur:
            reduced.append((cur, curb))
        elif curb:                      # 0 = 1  -> inconsistent (UNSAT)
            return (False, 0, len(reduced), steps)
    return (True, 0, len(reduced), steps)  # solvable (we only need SAT/UNSAT + rank here)

def tseitin_solvable(nv, charge, seed):
    """Tseitin on a random 3-regular graph: vertex v constraint = XOR of incident edge-vars = charge[v].
    Returns (solvable, num_edges, gaussian_steps)."""
    edges = three_regular_graph(nv, seed)
    ne = len(edges)
    # incidence matrix: row per vertex, column per edge
    A = [0] * nv
    for e_idx, (a, b) in enumerate(edges):
        A[a] ^= (1 << e_idx)
        A[b] ^= (1 << e_idx)
    solvable, _, rank, steps = gf2_solve(A, charge[:nv])
    return solvable, ne, steps

print("=== Layer 2 test: is the Tseitin/expander 'hard witness' hard for P? ===")
print("Tseitin(G, charge): edge variables; each vertex = XOR of incident edges = charge[v].")
print("HARD for resolution (BSW expander width lower bound = the repo's genuine asset).")
print("Now solve it with Gaussian elimination over GF(2) (a poly-time P algorithm):\n")
print(f"{'vertices':>8} {'edges':>6} | {'even-charge SAT':>16} {'odd-charge UNSAT':>17} | {'gaussian steps':>14} {'~E^2':>8}")
for nv in [10, 20, 40, 80, 160, 320]:
    even = [0]*nv                      # all-zero charge: satisfiable (all edges 0)
    odd = [0]*nv; odd[0] = 1           # single odd charge on a connected component => UNSAT
    s_even, ne, st_even = tseitin_solvable(nv, even, seed=7)
    s_odd,  _,  st_odd  = tseitin_solvable(nv, odd,  seed=7)
    print(f"{nv:>8} {ne:>6} | {str(s_even):>16} {str(not s_odd):>17} | {max(st_even,st_odd):>14} {ne*ne:>8}")

print("""
=== Verdict ===
Gaussian elimination decides every Tseitin instance in O(V*E) ~ O(E^2) steps -- POLYNOMIAL.
So Tseitin is IN P.  Its exponential hardness holds ONLY for resolution (a model that cannot do
linear algebra), not for general P-time computation.

Therefore the composite mu's Layer 2 (hard-side witness = Tseitin/expander rigidity):
  * is HIGH on Tseitin (resolution width is large), but
  * Tseitin is P-EASY (Gaussian elimination),
so mu would be HIGH on a P-solvable object => it does NOT witness NP-hardness-against-P.

The 'genuine lower-bound asset' is a RESOLUTION lower bound on a P-EASY object.  Building a
separating measure on it cannot work: Layer 2 has no object with a proven super-polynomial lower
bound against general P -- because such an object IS P != NP.  The composite collapses here, not at
the quotient.
""")
