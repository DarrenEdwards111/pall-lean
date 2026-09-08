# Exact exponential boundary-CNF lower bound

2026-09-08. Elementary mathematical proof below, finite checks supplied; not Lean verified. This is a representation lower bound, not a SAT runtime separation.

## Construction

For boundary variables x_1,...,x_n, introduce auxiliary variables p_1,...,p_n. Enforce p_1=x_1, p_i=p_{i-1} XOR x_i for i>=2, and p_n=1. Equality takes two binary clauses; each XOR gate takes four ternary clauses; the terminal condition is one unit clause. This is a width-at-most-three CNF F_n of 4n-1 clauses with 2n variables, hence polynomial encoded length (O(n log n) with explicit indices).

Existentially eliminating all p variables yields precisely odd parity on x. The construction has exactly one consistent p assignment for each odd x, and none for even x.

## Lower bound for CNF summaries on x alone

Any non-tautological clause implied by odd parity must mention every x variable. Otherwise falsify all its mentioned literals and use one unmentioned variable to adjust parity to odd. That gives an odd assignment falsifying the clause, a contradiction.

Every full-width non-tautological clause excludes exactly one assignment. An exact CNF for odd parity must exclude all 2^(n-1) even assignments. Therefore it needs at least 2^(n-1) distinct clauses. Taking one clause excluding each even assignment attains the bound.

Thus O(n) width-three constraints can have an existential boundary projection requiring exponentially many clauses if represented as a CNF over boundary variables alone. The exponential is in n; relative to explicit bit encoding length L=O(n log n), this is still superpolynomial, not necessarily 2^(Omega(L)).

## Why this does not prove unavoidable observer cost

The same projected relation has a linear-size XOR circuit and a constant-width ordered branching program: keep one parity bit as the x variables are read. The original extended CNF is itself a compact existential representation. A decider can retain that structure; it need not output a CNF without auxiliary variables.

This gives a precise separation between a large explicit boundary representation and cheap boundary processing. It rules out inferring runtime directly from the minimum size of an auxiliary-free CNF summary unless the model independently forces that representation. The tested family is satisfiable and has obvious witnesses; no unrestricted hardness is claimed.

## Checks

projection-check.py exhaustively checks the auxiliary-variable projection for n=2..7. It also enumerates all 3^n non-tautological clause patterns, confirming that the only implicates are the 2^(n-1) full-width clauses. These finite tests corroborate the general elementary proof above, but are not a formal proof assistant certificate.

## Remaining target

The construction proves a genuine exponential lower bound in one representation class. Extending it to all polynomial-time boundary representations fails here because of the explicit parity algorithm. A different family and an algorithm-independent necessity theorem remain required.
