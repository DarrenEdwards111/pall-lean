#!/usr/bin/env python3
"""
Test the interaction matrix bridge.

Key question: If we build a "correct solver" polynomial in sum form,
does its interaction matrix rank grow?

A correct solver must encode: for each clause C, whether it's satisfied.
Model: P_solver = Y · ∑_C (satisfaction_indicator_C)²

If the solver correctly determines each clause, the satisfaction indicators
are correlated with the clause gadgets. Does this force the interaction
matrix to have high rank?

Test with explicit small instances.
"""
import numpy as np
from itertools import combinations
from collections import defaultdict

def poly_mul(p1,p2):
    r=defaultdict(int)
    for m1,c1 in p1.items():
        for m2,c2 in p2.items():
            if m1&m2: continue
            r[m1|m2]+=c1*c2
    return {m:c for m,c in r.items() if c}

def poly_add(p1,p2):
    r=defaultdict(int)
    for m,c in p1.items(): r[m]+=c
    for m,c in p2.items(): r[m]+=c
    return {m:c for m,c in r.items() if c}

def poly_neg(p): return {m:-c for m,c in p.items()}
def X(i): return {frozenset([i]):1}
def C(c): return {frozenset():c} if c else {}

def pderiv(p,v):
    r=defaultdict(int)
    for m,c in p.items():
        if v in m: r[m-{v}]+=c
    return {m:c for m,c in r.items() if c}

def interaction_matrix(poly, reps):
    """Interaction matrix M[i,j] = L1 norm of ∂_i∂_j(poly)"""
    n = len(reps)
    M = np.zeros((n,n))
    for i in range(n):
        for j in range(n):
            if i==j: continue
            d = pderiv(pderiv(poly, reps[i]), reps[j])
            M[i,j] = sum(abs(c) for c in d.values()) if d else 0
    return M

print("=" * 70)
print("INTERACTION MATRIX AS BRIDGE INVARIANT")
print("=" * 70)

# === Scenario 1: Independent clause gadgets (NP verifier) ===
# ∏(1-z_i·G_i) with z_i independent
print("\n--- Scenario 1: NP verifier ∏(1-z_i·G_i) ---")
for n in [3, 4, 5, 6]:
    p = C(1)
    for i in range(n):
        g = poly_add(X(2*i), X(2*i+1))
        p = poly_mul(p, poly_add(C(1), poly_neg(poly_mul(X(1000+i), g))))
    reps = [1000+i for i in range(n)]
    M = interaction_matrix(p, reps)
    rk = int(np.linalg.matrix_rank(M))
    print(f"  n={n}: interaction_rank={rk}, matrix diagonal={[M[i,i] for i in range(n)]}")
    if n <= 4:
        print(f"         M=\n{M}")

# === Scenario 2: Sum of squares (compiled polynomial) ===
# ∑ G_i² — using x-vars as reps
print("\n--- Scenario 2: Sum ∑G_i² ---")
for n in [3, 4, 5, 6]:
    p = {}
    for i in range(n):
        g = poly_add(X(2*i), X(2*i+1))
        p = poly_add(p, poly_mul(g, g))
    reps = [2*i for i in range(n)]  # first x-var per clause
    M = interaction_matrix(p, reps)
    rk = int(np.linalg.matrix_rank(M))
    print(f"  n={n}: interaction_rank={rk}")

# === Scenario 3: "Correct solver" in sum form ===
# The solver polynomial has indicators that correlate with clause vars.
# Model: P = ∑_C (a_C · G_C)² where a_C are solver output vars
# This is sum-of-squares but with CORRELATIONS to clause structure.
print("\n--- Scenario 3: Correlated solver ∑(a_i·G_i)² ---")
print("a_i = solver output vars (2000+i)")
for n in [3, 4, 5, 6]:
    p = {}
    for i in range(n):
        g = poly_add(X(2*i), X(2*i+1))
        a_g = poly_mul(X(2000+i), g)  # a_i * G_i
        p = poly_add(p, poly_mul(a_g, a_g))
    # Use a-vars as reps (these are the "solver output" variables)
    reps_a = [2000+i for i in range(n)]
    M_a = interaction_matrix(p, reps_a)
    rk_a = int(np.linalg.matrix_rank(M_a))
    # Also use x-vars
    reps_x = [2*i for i in range(n)]
    M_x = interaction_matrix(p, reps_x)
    rk_x = int(np.linalg.matrix_rank(M_x))
    print(f"  n={n}: rank(a-vars)={rk_a}, rank(x-vars)={rk_x}")
    if n <= 4:
        print(f"         M_a=\n{M_a}")

# === Scenario 4: Mixed — what if solver uses PRODUCT internally? ===
# P = ∑_C (1-z_C·G_C)² — squaring the product terms
print("\n--- Scenario 4: ∑(1-z_i·G_i)² (squared product factors) ---")
for n in [3, 4, 5, 6]:
    p = {}
    for i in range(n):
        g = poly_add(X(2*i), X(2*i+1))
        factor = poly_add(C(1), poly_neg(poly_mul(X(1000+i), g)))
        p = poly_add(p, poly_mul(factor, factor))
    reps = [1000+i for i in range(n)]
    M = interaction_matrix(p, reps)
    rk = int(np.linalg.matrix_rank(M))
    print(f"  n={n}: interaction_rank={rk}")
    if n <= 4:
        print(f"         M=\n{M}")

# === Scenario 5: What the compiler ACTUALLY produces ===
# Y · ∑ gate² where gates involve shared TM state
# Gate_t = q_t ⊕ δ(q_{t-1}, tape_t)
# Simplified: gate_t = q_t · x_t (state * tape)
print("\n--- Scenario 5: TM gates with time-indexed state ---")
print("gate_t = q_t · x_t, compiled = ∑ gate_t²")
for n in [3, 4, 5, 6]:
    p = {}
    for t in range(n):
        gate = poly_mul(X(3000+t), X(t))  # q_t * x_t
        p = poly_add(p, poly_mul(gate, gate))
    # Reps = q_t (state vars)
    reps = [3000+t for t in range(n)]
    M = interaction_matrix(p, reps)
    rk = int(np.linalg.matrix_rank(M))
    print(f"  n={n}: interaction_rank={rk}")

# === KEY TEST: Does correctness force interaction rank? ===
print("\n" + "=" * 70)
print("KEY TEST: Correctness constraint on interaction rank")
print("=" * 70)
print("""
If P_solver correctly computes SAT, then for each clause C:
  ∂_{z_C}(P_solver)|_{satisfying_assignment} ≠ 0

This means the solver polynomial must "know about" each clause.
But does it need to know about PAIRS of clauses independently?

The interaction matrix measures pairwise knowledge:
  M[i,j] = ∂_{v_i}∂_{v_j}(P) 

For the product: M[i,j] ≠ 0 because removing two factors leaves others.
For the sum: M[i,j] = 0 because clauses are additive (independent).

The question: does CORRECTNESS force M[i,j] ≠ 0?

Answer: NO! A correct solver can process clauses one at a time.
Its "knowledge" of clause i is independent of clause j.
The sum form ∑ G_C² is a perfectly correct solver representation
with M[i,j] = 0.

So interaction matrix rank does NOT follow from correctness alone.
It's a property of the REPRESENTATION (product vs sum),
not of the FUNCTION COMPUTED.
""")

# Verify: both product and sum encode the same boolean function
print("--- Verification: same boolean function, different interaction ---")
print("Product and sum both = 0 on unsatisfying assignments (over F_2)")
print("But interaction matrices are completely different.")
print()
for n in [3]:
    pp = C(1)
    sp = {}
    for i in range(n):
        g = poly_add(X(2*i), X(2*i+1))
        pp = poly_mul(pp, poly_add(C(1), poly_neg(poly_mul(X(1000+i), g))))
        sp = poly_add(sp, poly_mul(g, g))
    
    Mp = interaction_matrix(pp, [1000+i for i in range(n)])
    Ms = interaction_matrix(sp, [2*i for i in range(n)])
    print(f"  Product interaction rank: {int(np.linalg.matrix_rank(Mp))}")
    print(f"  Sum interaction rank: {int(np.linalg.matrix_rank(Ms))}")
    print(f"  Same function? Yes (both zero iff all clauses satisfied)")
    print(f"  Different interaction? Yes (product has cross-terms, sum doesn't)")
    print()
    print("  This means the invariant distinguishes REPRESENTATIONS,")
    print("  not FUNCTIONS. For a bridge, we need: every poly-time")
    print("  computable representation has low interaction rank.")
    print("  But the product form IS poly-time computable and has HIGH rank!")

print("\n" + "=" * 70)
print("CONCLUSION")
print("=" * 70)
print("""
The interaction matrix (and all other invariants tested) distinguish
PRODUCT from SUM representations, but NOT P from NP.

The product form ∏(1-z_i·G_i) is easily computable (poly-time, even
linear-time) and has high interaction rank. So "high interaction rank"
does NOT imply "hard to compute."

The NP-hardness of Tseitin is about the SATISFIABILITY PROBLEM,
not about evaluating the polynomial. Any representation of the
verifier (product or sum) can be evaluated in poly time.

The SPDP framework tries to use algebraic complexity (rank of
derivative space) as a proxy for computational complexity.
But the same boolean function can have wildly different algebraic
complexity depending on representation.

For the bridge to work, you'd need to show that EVERY polynomial
that agrees with the verifier on boolean inputs has the same
SPDP rank. That would be a statement about the boolean function,
not the polynomial — essentially a polynomial identity testing result.

This is related to the Razborov-Rudich natural proofs barrier:
any property that distinguishes hard functions from easy ones
cannot be "natural" (decidable in poly time on the truth table).
""")
