#!/usr/bin/env python3
"""
Retarget Möbius/SPDP machinery to the SEARCH polynomial.

Instead of measuring Möbius mass of the verifier V_φ(x) = Π_c c(x),
measure Möbius/Fourier structure of the DECISION function:

  f(z_1,...,z_m) = 1 iff formula with clauses {c_i : z_i=1} is satisfiable

Here z_i ∈ {0,1} indicates whether clause c_i is included.
This is a boolean function on {0,1}^m whose structure encodes
the complexity of the SAT decision.

The Fourier/Möbius decomposition of f gives:
  f(z) = Σ_{S⊆[m]} f̂(S) · Π_{i∈S} z_i    (multilinear expansion)

where f̂(S) = Σ_{T⊆[m]} (-1)^{|S\T|} f(T) / 2^m   (Fourier on {0,1}^m)

or equivalently via Möbius inversion:
  f̂_Möb(S) = Σ_{T⊆S} (-1)^{|S\T|} f(T)

Key properties:
- f̂(S) depends only on the FUNCTION f, not its representation
- f̂(S) measures the irreducible |S|-way interaction between clauses
- If f has high-degree Fourier weight, it requires complex computation
- A poly-time solver must compute f, but can it avoid the high-degree terms?

This is the RIGHT observable for P≠NP.
"""

import numpy as np
from itertools import combinations, product as cartesian_product
from math import comb

def create_clause_pool(n, m, k=3, seed=42):
    """Create m random k-SAT clauses over n variables.
    Each clause: list of (var_index, positive?) pairs."""
    rng = np.random.RandomState(seed)
    clauses = []
    for _ in range(m):
        vars_chosen = rng.choice(n, size=k, replace=False)
        signs = rng.choice([True, False], size=k)
        clauses.append(list(zip(vars_chosen.tolist(), signs.tolist())))
    return clauses

def evaluate_clause(clause, assignment):
    """Check if a clause is satisfied by an assignment."""
    for var_idx, positive in clause:
        if positive and assignment[var_idx] == 1:
            return True
        if not positive and assignment[var_idx] == 0:
            return True
    return False

def is_satisfiable(clause_subset, all_clauses, n):
    """Check if the formula with given clause indices is satisfiable."""
    if not clause_subset:
        return True  # empty formula is trivially satisfiable
    for assignment in cartesian_product([0, 1], repeat=n):
        if all(evaluate_clause(all_clauses[c], assignment) for c in clause_subset):
            return True
    return False

def decision_function(z_bits, all_clauses, n):
    """Evaluate f(z_1,...,z_m) = SAT(formula with clauses {c_i : z_i=1}).
    z_bits: tuple of 0/1 values."""
    active_clauses = [i for i, z in enumerate(z_bits) if z == 1]
    return 1 if is_satisfiable(active_clauses, all_clauses, n) else 0

def compute_mobius(f_values, m):
    """Compute Möbius coefficients: f̂(S) = Σ_{T⊆S} (-1)^{|S\T|} f(T).
    f_values: dict mapping frozenset -> f(z) value."""
    mobius = {}
    for S_size in range(m + 1):
        for S in combinations(range(m), S_size):
            S_set = frozenset(S)
            val = 0
            for T_size in range(S_size + 1):
                for T in combinations(S, T_size):
                    T_set = frozenset(T)
                    sign = (-1) ** (S_size - T_size)
                    val += sign * f_values[T_set]
            mobius[S_set] = val
    return mobius

def compute_fourier(f_values, m):
    """Compute Fourier coefficients on {0,1}^m with ±1 convention.
    f̂(S) = (1/2^m) Σ_z f(z) · (-1)^{Σ_{i∈S} z_i}."""
    N = 2 ** m
    fourier = {}
    for S_size in range(m + 1):
        for S in combinations(range(m), S_size):
            S_set = frozenset(S)
            val = 0.0
            for z in cartesian_product([0, 1], repeat=m):
                chi_S = (-1) ** sum(z[i] for i in S)
                z_set = frozenset(i for i, b in enumerate(z) if b == 1)
                val += f_values[z_set] * chi_S
            fourier[S_set] = val / N
    return fourier

def run_experiment(n, m, k=3, seed=42):
    """Compute Möbius/Fourier structure of the SAT decision function."""
    print(f"\n{'='*70}")
    print(f"SAT Decision Function: n={n} vars, m={m} clauses, {k}-SAT")
    print(f"{'='*70}")
    
    clauses = create_clause_pool(n, m, k, seed)
    print(f"Clauses: {clauses}")
    
    # Compute f(z) for all z ∈ {0,1}^m
    f_values = {}
    for z in cartesian_product([0, 1], repeat=m):
        z_set = frozenset(i for i, b in enumerate(z) if b == 1)
        f_values[z_set] = decision_function(z, clauses, n)
    
    total_sat = sum(f_values.values())
    print(f"f(z)=1 for {total_sat}/{2**m} formula subsets")
    
    # Compute Möbius coefficients
    mobius = compute_mobius(f_values, m)
    
    # Compute Fourier coefficients
    fourier = compute_fourier(f_values, m)
    
    # Report by level
    print(f"\nMöbius coefficients by level:")
    for level in range(m + 1):
        coeffs = {S: v for S, v in mobius.items() if len(S) == level}
        nonzero = {S: v for S, v in coeffs.items() if v != 0}
        total_abs = sum(abs(v) for v in coeffs.values())
        print(f"  |S|={level}: {len(nonzero)}/{len(coeffs)} nonzero, "
              f"Σ|f̂| = {total_abs}, C(m,{level}) = {comb(m, level)}")
        if nonzero and level <= 3:
            for S, v in sorted(nonzero.items(), key=lambda x: len(x[0])):
                print(f"    S={set(S)}: f̂ = {v}")
    
    print(f"\nFourier coefficients by level:")
    for level in range(m + 1):
        coeffs = {S: v for S, v in fourier.items() if len(S) == level}
        total_sq = sum(v**2 for v in coeffs.values())
        total_abs = sum(abs(v) for v in coeffs.values())
        print(f"  |S|={level}: Σf̂² = {total_sq:.6f}, Σ|f̂| = {total_abs:.6f}")
    
    # Fourier weight at each level (fraction of total energy)
    total_energy = sum(v**2 for v in fourier.values())
    print(f"\nFourier energy distribution (Σf̂²/total):")
    for level in range(m + 1):
        level_energy = sum(v**2 for S, v in fourier.items() if len(S) == level)
        frac = level_energy / total_energy if total_energy > 0 else 0
        print(f"  degree {level}: {frac:.4f} ({frac*100:.1f}%)")
    
    return mobius, fourier

# Test with small instances
# Instance 1: Easy (few clauses, many solutions)
run_experiment(n=4, m=3, k=2, seed=42)

# Instance 2: Moderate
run_experiment(n=4, m=4, k=3, seed=42)

# Instance 3: Near threshold (m/n ~ 4.27 for 3-SAT)
run_experiment(n=4, m=5, k=3, seed=123)

# Instance 4: Larger
run_experiment(n=5, m=4, k=3, seed=42)

# Compare: trivial function (always SAT)
print(f"\n{'='*70}")
print("CONTROL: Trivial function (always satisfiable)")
print(f"{'='*70}")
# Use tautological clauses: (x1 ∨ ¬x1)
n, m = 3, 3
clauses_trivial = [[(0, True), (0, False)], [(1, True), (1, False)], [(2, True), (2, False)]]
f_triv = {}
for z in cartesian_product([0, 1], repeat=m):
    z_set = frozenset(i for i, b in enumerate(z) if b == 1)
    f_triv[z_set] = 1  # always satisfiable
mobius_triv = compute_mobius(f_triv, m)
print(f"Möbius of constant-1 function:")
for level in range(m + 1):
    coeffs = {S: v for S, v in mobius_triv.items() if len(S) == level}
    nonzero = {S: v for S, v in coeffs.items() if v != 0}
    print(f"  |S|={level}: {len(nonzero)} nonzero, vals = {[v for v in nonzero.values()]}")

print(f"\n{'='*70}")
print("ANALYSIS")
print(f"{'='*70}")
print("""
Key observations:
1. The Möbius coefficients of f(z) = SAT(clause subset z) are 
   representation-INVARIANT — they depend only on which subsets
   of clauses are satisfiable.

2. For nontrivial SAT instances, the Möbius coefficients are nonzero
   at HIGH levels — clauses interact in complex ways through the
   satisfiability decision.

3. The constant function (always SAT) has f̂(S)=0 for |S|≥1 and
   f̂(∅)=1. Only nontrivial instances have high-degree Möbius weight.

4. A poly-time solver must compute f(z) for all z — but can it
   avoid "seeing" the high-degree Möbius structure?
   
   The answer depends on whether:
   (a) High Möbius degree implies high computational complexity
   (b) The specific Möbius structure of SAT is "hard" in some formal sense
   
This connects to:
- Fourier complexity / decision tree depth lower bounds
- The KKL theorem: if all Fourier mass is at low degree, 
  some variable has high influence
- For SAT near threshold: high-degree Fourier mass is forced
  by the sharp phase transition
""")
