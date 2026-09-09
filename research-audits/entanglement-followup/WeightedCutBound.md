# General bound for normalized weighted-cut log rank

2026-09-09. Elementary proof; not Lean verified. No P != NP separation.

## Setup

Let q>=2 and let psi be a pure state of q qubits. Let C range over unordered nontrivial bipartitions, with nonnegative real weights w_C. Define

 E(psi) = SUM_C w_C log2 SchmidtRank_C(psi).

Assume every unordered pair of qubits {a,b} has separating load at most one:

 SUM_{C separating a,b} w_C <= 1.

This is a sufficient normalization making each arbitrary two-qubit unitary change E by at most two, by the earlier per-cut log-rank bound. It is not claimed necessary for every possible small-change invariant.

## Bound: E(psi) <= q-1

For a cut with smaller side size s, Schmidt rank <= 2^s, so log2 rank <= s. The cut separates s(q-s) unordered pairs. Since q-s>=q/2,

 log2 rank <= s <= (2/q) s(q-s).

Multiply by nonnegative w_C and sum. Swap the two finite sums to obtain

 E <= (2/q) SUM_{a<b} SUM_{C separating a,b} w_C
   <= (2/q) binom(q,2)
   = q-1.

Thus exponentially many cuts, with ANY nonnegative weights obeying the load condition, still give at most linear instantaneous energy. The same conclusion holds if weights are selected separately for each state while satisfying the same load constraint. Dynamic weight changes, however, need their own per-step accounting.

If pair loads are instead bounded by B, the same proof gives E <= B(q-1). The certified per-step bound is 2B. This does not prove that the smallest actual per-step bound equals 2B, and therefore does not bound E/r for an arbitrary sharper r. It does show that this particular normalization/certificate cannot directly produce a superpolynomial ratio on polynomially many explicit qubits.

## Sparse interaction graphs

If only edges of a fixed connected graph H are allowed operations and their loads are <=1, every nontrivial cut crosses at least one edge. Hence SUM_C w_C <= |E(H)| and E <= (q/2)|E(H)|, still polynomial for a simple graph. A sharper spanning-tree version gives SUM_C w_C <= q-1 and E <= q(q-1)/2, because every nontrivial cut crosses the spanning tree. Disconnected graphs need separate treatment: cuts between components have no constrained load, but local operations cannot create entanglement across those component cuts from a product initial state.

## Limits

This result concerns weighted sums of ordinary Schmidt log ranks on a fixed finite qubit system. It does not refute the full N-Frame Lagrangian, virtual exponentially large state spaces, signed-weight constructions, or an accumulated path-cost invariant. Each requires a separate faithful link to actual machine operations. Proving unavoidable superpolynomial accumulated cost would still require a SAT-specific lower bound.

No numerical tests are used as a substitute for this all-weights argument. The proof uses the Hilbert-space dimension bound and finite double counting.
