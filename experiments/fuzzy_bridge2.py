#!/usr/bin/env python3
"""
Deeper analysis: what observable IS representation-invariant 
AND grows superpolynomially for hard functions?

The interaction information approach has a problem: for AND,
the per-subset interaction is O(1/2^n), so total is small.

But the fuzzy-graph framework suggests a DIFFERENT observable:
the GRAPH STRUCTURE of the computation.

Key idea from fuzzy-graph AGI:
- Graph memory tracks which predicates CO-ACTIVATE
- Meta-predicates form over CLUSTERS of co-activating predicates
- The COMMUNITY STRUCTURE of the graph is the invariant

For P≠NP, the relevant invariant is:
- NOT the interaction information (too weak for AND)
- NOT the Möbius mass (representation-dependent)
- The COMMUNICATION COMPLEXITY between variable groups

A function f(x_1,...,x_n) requires k-party communication complexity
C_k if any k parties, each holding a subset of variables, must 
exchange C_k bits to compute f.

AND: any party missing even 1 variable must receive it → Ω(n) comm.
But this doesn't scale superpolynomially.

OK, let me think differently. What does fuzzy-graph ACTUALLY do
that standard approaches don't?

1. MULTI-CANDIDATE GENERATION + SELECTION
   - LLM proposes multiple solutions
   - Code-based selector VERIFIES each
   - Only verified solutions pass

2. FUZZY EVALUATION
   - Not just 0/1 but continuous [0,1]
   - Captures "how close" to correct

3. GRAPH MEMORY
   - Tracks correlations between concepts
   - Builds STRUCTURAL model of relationships

Applied to P≠NP:
- The polynomial is the "LLM proposal" — many possible representations
- The boolean function is the "selector" — only correct ones pass
- The question: among all correct representations, is there one 
  that's "simple" (poly-size)?

The fuzzy-graph insight for the bridge:
DON'T measure the polynomial. Measure the COMPUTATION GRAPH.

A Turing machine computing f has a computation graph G:
- Nodes = intermediate values (tape cells at each step)
- Edges = dependencies (which values depend on which)
- The graph has T·S nodes (T steps × S space)

The BOOLEAN sensitivity of f measures how many graph edges are 
"essential" — if we remove them, the output changes.

For AND: every input is essential → at least n essential edges.
But a TM with T steps has ≤ T edges per step → total edges ~ T.
If T = poly(n), total edges = poly(n) ≥ n. No contradiction.

The scaling needs to be SUPERPOLYNOMIAL in the number of essential
interactions, not just polynomial.

Actually... let me revisit the SPDP approach with the fuzzy lens.

SPDP says: the compiled polynomial has RANK (number of independent
product components). The question is whether rank is preserved
under compilation.

The fuzzy-graph says: don't look at the polynomial. Look at the
STRUCTURE of the computation.

What if the "rank" is not of the polynomial, but of the 
COMPUTATION DAG?

A TM with T steps and S space has a DAG with:
- Inputs: x_1, ..., x_n
- Intermediates: tape cells at each step
- Output: accept/reject

The "product complexity" of this DAG is:
how many INDEPENDENT PATHS are needed to cover all input-output connections?

For AND: every input connects to the output → n independent paths.
For a sequential TM: O(1) active paths at any time (bounded space).

If we define "path width" as the maximum number of simultaneously
active independent paths through the DAG, then:
- AND requires path width n (all inputs contribute)
- A poly-time TM has path width ≤ S (space bound)
- P = poly-time + poly-space → path width ≤ poly(n)
- If AND requires path width 2^Ω(n)... no, AND only needs width n.

This doesn't work either. AND is too simple — it's computable in
linear time, so it CAN'T separate P from NP.

WAIT. That's the fundamental issue. We're trying to show that
computing AND of n clauses is hard, but AND IS EASY (linear time).
The hard part is SATISFIABILITY — given a CNF formula, determine
if ANY assignment makes it true.

The SAT function is:
  SAT(φ) = ∃x: φ(x) = true
  SAT(φ) = OR_{x ∈ {0,1}^n} AND_{clauses c} c(x)

The outer OR over 2^n assignments is what makes it hard.

So the polynomial we should be looking at is NOT just
Π(1-G_i) (the Tseitin product for one assignment).

It's the ENTIRE SAT polynomial:
  p(φ) = 1 - Π_x (1 - Π_c c(x))   or similar

This requires 2^n products — one per potential assignment.
A poly-time solver would need to somehow evaluate this without
enumerating all assignments.

The SPDP framework was measuring the polynomial for a FIXED input x,
i.e., "verify that THIS assignment satisfies ALL clauses."
That's verification, not search. Verification IS easy (linear time).

The P≠NP question is about SEARCH, not verification.
The compiled polynomial should represent the SEARCH process,
not the verification process.

For a SAT solver M:
- Input: clause descriptions (the formula φ)
- Output: SAT/UNSAT
- The compiled polynomial encodes the ENTIRE search, not just verification.

The Tseitin encoding of M's computation:
  p_M = Π_{t=1}^T (1 - c_t(tape_t, tape_{t+1})²)

where tape_t includes BOTH the input formula description AND
the solver's intermediate state.

The "content variables" are the clause truth values for a SPECIFIC
assignment found by the solver. But the solver searches over assignments!

I think the SPDP framework conflated:
1. Verification polynomial: does THIS assignment satisfy?
2. Search polynomial: does ANY assignment satisfy?

The verification polynomial is easy (linear in n).
The search polynomial is what P≠NP is about.
"""

print("="*70)
print("CRITICAL REALIZATION")
print("="*70)
print("""
The SPDP/Möbius framework has been measuring the VERIFICATION
polynomial, not the SEARCH polynomial.

Verification: "Check if assignment x satisfies all n clauses"
  → Π(1-G_i): product of n terms → linear time → NOT hard
  → ANY solver can verify in O(n) → mass is always achievable

Search: "Find if ANY assignment satisfies the formula"
  → Requires exploring 2^n possible assignments
  → The hard part is the EXISTENTIAL QUANTIFIER

The correct polynomial for P≠NP should encode the SEARCH,
including the ∃x quantifier. This is:
  
  SAT(φ) = Σ_{x ∈ {0,1}^n} Π_{clauses c} c(x)
            (counts satisfying assignments)
  
  or the 0/1 version:
  1 - Π_{x} (1 - Π_c c(x))
  
The Tseitin encoding of a SAT SOLVER includes the search:
  p_M = Π_{t=1}^T (1 - transition_t²)
  
where T ~ poly(n) steps explore the assignment space.
The content variables here should be the CLAUSE DESCRIPTIONS
(input to the solver), not individual variable assignments.

This changes everything about what we measure.

The fuzzy-graph insight: the SELECTOR evaluates proposals.
In SAT, the "proposal" is an assignment, and the "selector"
checks if it satisfies all clauses. The SEARCH for a good
proposal is the hard part — that's where computation happens.

To prove P≠NP, measure the complexity of SEARCH, not verification.
""")

# Let's compute what the SAT polynomial looks like
from itertools import product as cartesian_product

def sat_polynomial_eval(clause_matrix, x):
    """Evaluate SAT polynomial: Π_{clauses c} c(x) for a specific x.
    clause_matrix[i][j] = 1 if variable j appears positive in clause i,
                         -1 if negative, 0 if absent.
    """
    result = 1
    for clause in clause_matrix:
        clause_sat = 0
        for j, lit in enumerate(clause):
            if lit == 1 and x[j] == 1:
                clause_sat = 1
                break
            if lit == -1 and x[j] == 0:
                clause_sat = 1
                break
        result *= clause_sat
    return result

def count_sat(clause_matrix, n):
    """Count satisfying assignments = Σ_x Π_c c(x)."""
    count = 0
    for x in cartesian_product([0, 1], repeat=n):
        count += sat_polynomial_eval(clause_matrix, x)
    return count

# Example: 3-SAT on 4 variables, 4 clauses
# (x1 ∨ x2 ∨ x3), (¬x1 ∨ x3 ∨ x4), (x2 ∨ ¬x3 ∨ x4), (¬x2 ∨ ¬x3 ∨ ¬x4)
clauses = [
    [1, 1, 1, 0],   # x1 ∨ x2 ∨ x3
    [-1, 0, 1, 1],  # ¬x1 ∨ x3 ∨ x4
    [0, 1, -1, 1],  # x2 ∨ ¬x3 ∨ x4
    [0, -1, -1, -1], # ¬x2 ∨ ¬x3 ∨ ¬x4
]
n = 4
sat_count = count_sat(clauses, n)
print(f"\nExample 3-SAT instance: {len(clauses)} clauses, {n} vars")
print(f"Satisfying assignments: {sat_count} out of {2**n}")
print(f"\nThe #SAT polynomial is Σ_x Π_c c(x) = {sat_count}")
print(f"The SAT decision is: {sat_count > 0}")
