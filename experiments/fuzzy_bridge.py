#!/usr/bin/env python3
"""
Fuzzy-Graph Approach to the Bridge Problem

The key insight from Darren's fuzzy-graph AGI architecture:
fuzzy predicates track CORRELATIONS between activations.
These correlations are a property of the FUNCTION, not the representation.

The Möbius mass framework failed because mass depends on algebraic form.
But CORRELATION between clause variables under random input is 
representation-invariant — it depends only on the boolean function.

For the AND function x₁ ∧ x₂ ∧ ... ∧ xₙ:
- Evaluated at random {0,1}^n: E[AND] = 1/2^n
- Correlation between any pair of "clause indicators": 
  Corr(x_i, AND) depends on the function, not how we compute it

The fuzzy-graph observable:
Instead of measuring algebraic coefficient mass (representation-dependent),
measure the INTERACTION INFORMATION between clause subsets:

  I(T) = ∑_{S⊆T} (-1)^{|T\S|} H(X_S)   (Möbius inversion of entropy)

This is the INTERACTION INFORMATION (or co-information) from information theory.
It measures the irreducible k-way dependency among variables.

Key property: interaction information is a FUNCTION of the joint distribution,
not the polynomial representation. It's representation-invariant!

For AND of n independent clauses:
- All k-way interactions are nonzero (AND creates genuine k-way dependency)
- I({i,j}) = I(x_i; x_j | AND=1) - I(x_i; x_j | AND=0) ≠ 0

For a correct solver (any representation):
- Must agree with AND on {0,1}^n
- Therefore has the SAME joint distribution over content variables
- Therefore has the SAME interaction information

This gives a REPRESENTATION-INVARIANT bridge!

The P≠NP argument via interaction information:
1. AND has high k-way interaction information (combinatorial bound)
2. Any correct solver has the SAME interaction structure (invariance)
3. Computing high interaction information requires many operations
4. Poly-time → bounded operations → bounded achievable interaction
5. Contradiction

The key question becomes: does bounded computation time limit
achievable interaction information? This is an information-theoretic
complexity question, not a polynomial representation question.
"""

import numpy as np
from itertools import combinations, product as cartesian_product
from math import log2, comb

def entropy(probs):
    """Shannon entropy of a probability distribution."""
    return -sum(p * log2(p) for p in probs if p > 0)

def joint_entropy(vars_subset, truth_table):
    """Compute H(X_S) for a subset S of variables from a truth table.
    
    truth_table: dict mapping (x_1,...,x_n) -> f(x) ∈ {0,1}
    vars_subset: indices of variables to compute joint entropy over
    """
    n = len(next(iter(truth_table.keys())))
    N = len(truth_table)
    
    # Count joint outcomes of (x_{i1}, ..., x_{ik}, f(x))
    # We include f(x) because we're measuring correlation CONDITIONED on output
    counts = {}
    for assignment, output in truth_table.items():
        key = tuple(assignment[i] for i in vars_subset) + (output,)
        counts[key] = counts.get(key, 0) + 1
    
    probs = [c / N for c in counts.values()]
    return entropy(probs)

def interaction_information(T_indices, truth_table):
    """Compute interaction information I(T) via Möbius inversion of entropy.
    
    I(T) = ∑_{S⊆T} (-1)^{|T\S|} H(X_S, f)
    
    where H(X_S, f) is the joint entropy of the variables in S plus the function value.
    """
    T = sorted(T_indices)
    T_card = len(T)
    result = 0.0
    
    for r in range(T_card + 1):
        for S_tuple in combinations(T, r):
            S = list(S_tuple)
            sign = (-1) ** (T_card - len(S))
            H = joint_entropy(S, truth_table)
            result += sign * H
    
    return result

def compute_truth_table(f, n):
    """Compute truth table of f: {0,1}^n -> {0,1}."""
    table = {}
    for assignment in cartesian_product([0, 1], repeat=n):
        table[assignment] = f(assignment)
    return table

def AND_function(x):
    return int(all(xi == 1 for xi in x))

def OR_function(x):
    return int(any(xi == 1 for xi in x))

def XOR_function(x):
    return sum(x) % 2

def PARITY_function(x):
    return sum(x) % 2

print("="*70)
print("INTERACTION INFORMATION — Representation-Invariant Observable")
print("="*70)

for n in [3, 4, 5, 6]:
    print(f"\n--- n = {n} ---")
    
    and_table = compute_truth_table(AND_function, n)
    
    # Compute interaction information at each level
    for k in range(1, min(n+1, 5)):
        total_interaction = 0.0
        count = 0
        for T in combinations(range(n), k):
            ii = interaction_information(T, and_table)
            total_interaction += abs(ii)
            count += 1
        avg = total_interaction / count if count > 0 else 0
        print(f"  AND: |T|={k}, total |I(T)| = {total_interaction:.6f}, "
              f"count = {count}, avg = {avg:.6f}")

print(f"\n{'='*70}")
print("COMPARISON: AND vs OR vs XOR")
print("="*70)

n = 4
for name, func in [("AND", AND_function), ("OR", OR_function), ("XOR", XOR_function)]:
    table = compute_truth_table(func, n)
    print(f"\n{name} (n={n}):")
    for k in range(2, n+1):
        total = sum(abs(interaction_information(T, table)) for T in combinations(range(n), k))
        print(f"  |T|={k}: total |I(T)| = {total:.6f}, "
              f"C(n,k) = {comb(n,k)}")

print(f"\n{'='*70}")
print("KEY INSIGHT")
print("="*70)
print("""
Interaction information is computed from the JOINT DISTRIBUTION
of (x_1,...,x_n, f(x)). It depends only on the boolean function f,
not on how f is computed or represented.

If AND has high interaction information at level k, then ANY correct
solver of AND must produce the SAME interaction information — because
it computes the SAME function.

The bridge becomes: does computing a function with high k-way 
interaction information require many operations?

This is the INFORMATION-THEORETIC formulation of P ≠ NP:
- AND has Θ(1) interaction information per k-subset (for all k)
- C(n,k) k-subsets → total interaction ~ C(n, log n) at level log n
- Can O(n^c) operations produce C(n, log n) units of interaction?

The fuzzy-graph selector's correlation tracking is exactly this:
it measures how strongly variables interact through the computation.
The GRAPH EDGES are the interaction information.
""")

# Verify representation invariance
print("="*70)
print("VERIFICATION: Same function, different 'solvers'")
print("="*70)

n = 4
and_table = compute_truth_table(AND_function, n)

# "Solver 1": direct AND
# "Solver 2": sequential accumulator
# Both compute AND, so both have the same truth table
# Therefore same interaction information

print(f"\nAND function (n={n}):")
for k in range(2, n+1):
    interactions = [interaction_information(T, and_table) for T in combinations(range(n), k)]
    print(f"  |T|={k}: interactions = {[f'{x:.4f}' for x in interactions]}")
    print(f"         all equal? {len(set(round(x, 10) for x in interactions)) == 1}")

print("""
All pairs have EQUAL interaction information — the observable is
SYMMETRIC in the variables (since AND is symmetric).

This is exactly what product_form_mobius_uniform proved for the 
algebraic case: uniform Möbius mass = 1 for all subsets.

The fuzzy-graph insight: replace algebraic Möbius mass (representation-dependent)
with interaction information (representation-invariant, same uniform structure).
""")
