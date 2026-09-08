# Hard-family attempt: Tseitin parity contradictions

2026-09-08. Outcome: restricted proof-complexity candidate, not unrestricted SAT hardness. No Lean verification or P != NP proof.

## Why this family

For a graph G, associate a bit x_e to each edge and impose XOR_{e incident v} x_e = b_v at each vertex. A region's equations combine into a condition on its boundary edges. This directly supplies a mathematical boundary constraint rather than an arbitrary energy number. For bounded degree, converting each vertex constraint to CNF costs only constantly many clauses.

For degree three, exclude each of the four parity-violating local assignments by a three-literal clause. There are four clauses per vertex.

## Actual derived contradiction

XOR all vertex equations. Each edge occurs exactly twice, so the left side cancels to zero. If XOR_v b_v = 1, the right side is one. Thus the system is unsatisfiable. This proof works for any finite loop-free undirected graph with odd total charge.

For any vertex set S, XOR its equations: internal edges cancel and the remaining equation is XOR_{e in delta(S)} x_e = XOR_{v in S} b_v. Many boundary variables need not mean independent unresolved constraints: this is one parity equation, represented compactly.

## Why this does not finish the separation

Suitable expanding graph families have exponential resolution proof-size lower bounds. Reference: Ben-Sasson and Wigderson, Short Proofs are Narrow -- Resolution made Simple, https://www.math.ias.edu/avi/node/883 and the authors' overview https://www.ias.edu/math/csdm/98-99/abstracts . This attempt does not reprove that theorem, and the small graphs below are not asserted to be an asymptotic expander construction.

Resolution hardness does not constrain arbitrary deciders. Once the parity structure is given or recovered, the odd-charge contradiction is immediate by the sum above; arbitrary linear systems over GF(2) admit polynomial Gaussian elimination. With a canonical encoding, validating the local parity clause groups and incidence pairing is polynomial too. Hence a general SAT algorithm can recognize these canonical instances, use the shortcut, and use a complete solver for other inputs. No universal superpolynomial bound can rest on these canonical odd-charge instances alone.

Separate observers do not prevent a decider from performing algebra within its own workspace. Excluding Gaussian elimination or charging one bit per eliminated assignment would impose an additional restriction needing proof.

## Computational checks

parity-family-check.py checks every edge assignment and every vertex charge on K4 and K3,3. It verifies CNF/parity equivalence, unsatisfiability for odd charge, and satisfiability for even charge on these connected graphs. These finite tests do not establish a proof-size lower bound.

## What a next candidate must add

A hard-family argument must survive compact algebraic summaries, rather than just resolution or local consistency. Random 3-CNF or non-linear constraints could be investigated, but invoking their hardness without a universal lower-bound proof would just restate the gap. No such bound is claimed here.
