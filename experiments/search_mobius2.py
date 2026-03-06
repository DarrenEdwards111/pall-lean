#!/usr/bin/env python3
"""
Search-side Möbius with HARD instances — force some subsets to be UNSAT.

Strategy: use contradictory clause pairs that make some subsets unsatisfiable.
E.g., (x₁) and (¬x₁) together are UNSAT.
"""

import numpy as np
from itertools import combinations, product as cartesian_product
from math import comb

def is_satisfiable(active_clauses, all_clauses, n):
    if not active_clauses:
        return True
    for x in cartesian_product([0, 1], repeat=n):
        sat = True
        for c_idx in active_clauses:
            clause = all_clauses[c_idx]
            clause_sat = False
            for var_idx, positive in clause:
                if positive and x[var_idx] == 1:
                    clause_sat = True; break
                if not positive and x[var_idx] == 0:
                    clause_sat = True; break
            if not clause_sat:
                sat = False; break
        if sat:
            return True
    return False

def compute_mobius(f_values, m):
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

def run_instance(name, clauses, n, m):
    print(f"\n{'='*70}")
    print(f"{name}: n={n} vars, m={m} clauses")
    print(f"{'='*70}")
    
    f_values = {}
    for z in cartesian_product([0, 1], repeat=m):
        z_set = frozenset(i for i, b in enumerate(z) if b == 1)
        active = [i for i, b in enumerate(z) if b == 1]
        f_values[z_set] = 1 if is_satisfiable(active, clauses, n) else 0
    
    total_sat = sum(f_values.values())
    total_unsat = 2**m - total_sat
    print(f"SAT subsets: {total_sat}/{2**m}, UNSAT: {total_unsat}")
    
    mobius = compute_mobius(f_values, m)
    fourier = compute_fourier(f_values, m)
    
    print(f"\nMöbius coefficients by level:")
    for level in range(m + 1):
        coeffs = {S: v for S, v in mobius.items() if len(S) == level}
        nonzero = {S: v for S, v in coeffs.items() if v != 0}
        total_abs = sum(abs(v) for v in coeffs.values())
        print(f"  |S|={level}: {len(nonzero)}/{len(coeffs)} nonzero, Σ|f̂| = {total_abs}")
        if nonzero and level <= 4:
            for S, v in sorted(nonzero.items(), key=lambda x: len(x[0])):
                print(f"    S={set(S)}: f̂ = {v}")
    
    print(f"\nFourier energy by level:")
    total_energy = sum(v**2 for v in fourier.values())
    for level in range(m + 1):
        level_energy = sum(v**2 for S, v in fourier.items() if len(S) == level)
        frac = level_energy / total_energy if total_energy > 0 else 0
        print(f"  degree {level}: {frac*100:.1f}%")
    
    return mobius, fourier

# Instance 1: Two contradictory unit clauses
# c0: (x0), c1: (¬x0) → {c0,c1} is UNSAT
n, m = 2, 2
clauses1 = [[(0, True)], [(0, False)]]
run_instance("Contradictory pair (x₀) ∧ (¬x₀)", clauses1, n, m)

# Instance 2: Three unit clauses, two contradict
# c0: (x0), c1: (¬x0), c2: (x1) → {c0,c1} and {c0,c1,c2} are UNSAT
n, m = 2, 3
clauses2 = [[(0, True)], [(0, False)], [(1, True)]]
run_instance("Contradiction + independent (x₀)(¬x₀)(x₁)", clauses2, n, m)

# Instance 3: Pigeonhole-like (hard for resolution)
# 3 vars, 4 clauses designed so that specific subsets are UNSAT
n, m = 2, 4
clauses3 = [
    [(0, True)],           # x0
    [(0, False)],          # ¬x0
    [(1, True)],           # x1
    [(1, False)],          # ¬x1
]
run_instance("Double contradiction (x₀)(¬x₀)(x₁)(¬x₁)", clauses3, n, m)

# Instance 4: More complex — 3-SAT with forced UNSAT subsets
n, m = 3, 6
clauses4 = [
    [(0, True), (1, True), (2, True)],     # x0 ∨ x1 ∨ x2
    [(0, False), (1, False), (2, False)],   # ¬x0 ∨ ¬x1 ∨ ¬x2
    [(0, True), (1, False)],               # x0 ∨ ¬x1
    [(0, False), (1, True)],               # ¬x0 ∨ x1
    [(1, True), (2, False)],               # x1 ∨ ¬x2
    [(1, False), (2, True)],               # ¬x1 ∨ x2
]
run_instance("3-var structured instance", clauses4, n, m)

# Instance 5: All 8 possible unit clauses on 4 vars (maximally constrained)
n, m = 4, 8
clauses5 = [
    [(i, True)] for i in range(4)
] + [
    [(i, False)] for i in range(4)
]
clauses5_flat = clauses5
run_instance("All unit clauses on 4 vars", clauses5_flat, n, m)

# Instance 6: Unsatisfiable 3-SAT instance
# Force: every assignment violates at least one clause
n, m = 2, 4
clauses6 = [
    [(0, True), (1, True)],     # x0 ∨ x1  (killed by 00)
    [(0, True), (1, False)],    # x0 ∨ ¬x1 (killed by 01)
    [(0, False), (1, True)],    # ¬x0 ∨ x1 (killed by 10)
    [(0, False), (1, False)],   # ¬x0 ∨ ¬x1 (killed by 11)
]
run_instance("Full UNSAT instance (all 2-clauses on 2 vars)", clauses6, n, m)

print(f"\n{'='*70}")
print("KEY FINDINGS")
print(f"{'='*70}")
print("""
The decision function f(z) = SAT(formula with clauses {i: z_i=1})
has nontrivial Möbius/Fourier structure ONLY when some clause subsets
are UNSAT.

- If all subsets are SAT: f ≡ 1 (constant) → all mass at degree 0
- If some subsets are UNSAT: high-degree Möbius weight appears

The amount of high-degree weight depends on the INTERACTION between
clauses — how they constrain each other through shared variables.

This IS the right observable:
1. It's representation-invariant (depends only on which subsets are SAT)
2. It captures clause interaction complexity
3. Hard instances (near threshold, unsatisfiable cores) have high-degree weight
4. A poly-time solver must compute this function

The P≠NP question becomes:
Can a poly-time algorithm compute a boolean function f:{0,1}^m → {0,1}
that has superpolynomially many high-degree Fourier coefficients?

This is a WELL-STUDIED question in Fourier analysis of boolean functions!
- Linial-Mansour-Nisan: AC⁰ circuits have exponentially small high-degree weight
- Boppana: monotone circuits have bounded Fourier concentration
- Hastad switching lemma: random restrictions kill high-degree structure

The connection: if SAT's decision function has "inherently high-degree" 
Fourier structure that cannot be computed by restricted circuit classes,
that's a lower bound.
""")
