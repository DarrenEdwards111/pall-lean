# Nonlinear boundary summaries: exact elimination test

2026-09-08. Not Lean verified. No unrestricted SAT lower bound.

## Candidate and constructive test

Try forcing exponentially large boundary tables using non-affine clauses on a graph with large separators. Non-affine means not a system of parity equations: for example a two-literal OR relation has three allowed assignments and is not an affine subspace over GF(2).

But 2-CNF admits compact exact boundary summaries. Write a formula involving x as F0 AND AND_i(x OR a_i) AND AND_j(NOT x OR b_j), where a_i,b_j are literals or empty clauses. Then

    EXISTS x F = F0 AND AND_{i,j}(a_i OR b_j).

Proof: necessity is resolution. For sufficiency, if any a_i is false, choose x=true; all b_j must then be true by the pairwise clauses. If no a_i is false, choose x=false. Empty sides are handled by the same rule. Tautological clauses can be discarded.

Each resolvent still has width at most two. After deduplication, there are O(n^2) possible clauses, including units and the empty clause, throughout elimination. A simple finite-set implementation is polynomial time. There is no need to materialize the 2^b assignments to a b-variable boundary.

The primal graph can be complete (put a positive binary clause on every variable pair), so large graph separators do not by themselves defeat this representation. This example is easy and is used only to reject the proposed structural sufficiency criterion, not to dismiss possible worst-case SAT hardness.

## Where 3-CNF differs

Eliminating x from (x OR a OR b) AND (NOT x OR c OR d) produces the four-literal clause (a OR b OR c OR d). Width-two closure fails. Repeated elimination can increase widths and generate many clauses.

This does not prove every algorithm requires large resources: it only identifies failure of this particular bounded-width summary representation. A lower bound for all exact summaries with efficiently computable updates needs additional mathematics. Defining the energy as the size of this table would charge an implementation choice, not an unavoidable cost.

## Tests

nonlinear-boundary-check.py exhaustively examines all 4,096 subsets of the 12 non-tautological binary clauses on three distinct variables. It verifies 49,152 pointwise one-variable elimination equivalences and 4,096 complete decision results against brute force. This is a correctness sanity check for a standard elimination identity, not asymptotic experimental evidence of hardness.

Background on efficient 2-SAT algorithms: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2016.27 (research paper with classical 2-SAT references). The exact elimination proof above is included explicitly.

## Status

Nonlinearity plus a large separator is insufficient for the proposed lower bound. The missing step remains excluding every polynomial-cost representation/update strategy on a genuinely hard family, not merely observing clause growth in one strategy.
