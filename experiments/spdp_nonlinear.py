#!/usr/bin/env python3
"""
Nonlinear channels that flip zero/nonzero semantics.

Product: nonzero on satisfying assignments (encodes SAT as nonvanishing)
Sum: zero on satisfying assignments (encodes SAT as vanishing)

Channel candidates:
1. Complement: p → 1 - p (flips zero/nonzero on {0,1})
2. Möbius inversion on boolean lattice
3. Inclusion-exclusion: ∑G² → ∏(1-G²) 
4. Exponential map: ∑G² → exp(-∑G²) ≈ ∏(1-G²+...) truncated
5. Boolean interpolation: construct product from sum via truth table
"""
import numpy as np
from itertools import combinations, product as cartprod
from collections import defaultdict

# Multilinear poly arithmetic
def poly_mul(p1,p2):
    r=defaultdict(int)
    for m1,c1 in p1.items():
        for m2,c2 in p2.items():
            if m1&m2:continue
            r[m1|m2]+=c1*c2
    return {m:c for m,c in r.items() if c}

def poly_add(p1,p2):
    r=defaultdict(int)
    for m,c in p1.items():r[m]+=c
    for m,c in p2.items():r[m]+=c
    return {m:c for m,c in r.items() if c}

def poly_neg(p): return {m:-c for m,c in p.items()}
def poly_scale(p,s): return {m:c*s for m,c in p.items() if c*s}
def X(i): return {frozenset([i]):1}
def C(c): return {frozenset():c} if c else {}

def pderiv(p,v):
    r=defaultdict(int)
    for m,c in p.items():
        if v in m: r[m-{v}]+=c
    return {m:c for m,c in r.items() if c}

def poly_eval(p, assignment):
    result = 0
    for m, c in p.items():
        val = c
        skip = False
        for v in m:
            if v not in assignment:
                skip = True; break
            val *= assignment[v]
        if skip: continue
        result += val
    return result

def spdp_rank(poly, variables, kappa):
    derivs = []
    for combo in combinations(variables, kappa):
        d = poly
        for v in combo:
            d = pderiv(d, v)
            if not d: break
        if d: derivs.append(d)
    if not derivs: return 0
    all_m = sorted(set().union(*(d.keys() for d in derivs)), key=lambda s:(len(s),tuple(sorted(s))))
    mi = {m:i for i,m in enumerate(all_m)}
    mat = np.zeros((len(derivs),len(all_m)))
    for i,d in enumerate(derivs):
        for m,c in d.items(): mat[i,mi[m]]=c
    return int(np.linalg.matrix_rank(mat))

def get_vars(p):
    return sorted(set().union(*(m for m in p.keys() if m)))

# Gadget: G_i = x_{2i} · x_{2i+1} (AND gate, multilinear)
# Satisfied (G=1) when both true, G=0 otherwise
# Use simpler gadget for cleaner algebra
def gadget_and(i):
    return poly_mul(X(2*i), X(2*i+1))

# Gadget: G_i = 1 - x_{2i}·(1-x_{2i+1}) - x_{2i+1}·(1-x_{2i})  
# = 1 - x_{2i} - x_{2i+1} + 2·x_{2i}·x_{2i+1}
# This equals 1 when x_{2i}=x_{2i+1}, 0 when they differ
# "clause satisfied" = variables agree (XOR=0)
def gadget_eq(i):
    a, b = X(2*i), X(2*i+1)
    # 1 - a - b + 2ab (multilinear)
    return poly_add(poly_add(poly_add(C(1), poly_neg(a)), poly_neg(b)),
                    poly_scale(poly_mul(a, b), 2))

# Simple gadget: G_i = x_{2i} (satisfied when x_{2i}=1)
def gadget_simple(i):
    return X(2*i)

print("=" * 70)
print("NONLINEAR CHANNEL EXPERIMENTS")
print("=" * 70)

# === Channel 1: Inclusion-exclusion product ===
# Transform: ∑G_i → ∏(1-G_i)
# If G_i ∈ {0,1} on boolean inputs:
#   ∑G_i = 0 ⟺ all G_i=0 ⟺ ∏(1-G_i) = 1
#   ∑G_i > 0 ⟺ some G_i=1 ⟺ ∏(1-G_i) = 0

print("\n--- Channel 1: ∑G_i ↔ ∏(1-G_i) (inclusion-exclusion) ---")
print("Using simple gadget G_i = x_{2i}")
for n in range(2, 7):
    # Sum form
    s = C(0)
    for i in range(n):
        s = poly_add(s, gadget_simple(i))
    
    # Product form via inclusion-exclusion
    p = C(1)
    for i in range(n):
        p = poly_mul(p, poly_add(C(1), poly_neg(gadget_simple(i))))
    
    s_vars = get_vars(s)
    p_vars = get_vars(p)
    
    sr1 = spdp_rank(s, s_vars, 1)
    pr1 = spdp_rank(p, p_vars, 1)
    sr2 = spdp_rank(s, s_vars, 2) if len(s_vars) >= 2 else 0
    pr2 = spdp_rank(p, p_vars, 2) if len(p_vars) >= 2 else 0
    
    print(f"  n={n}: sum_rank(1,2)=({sr1},{sr2})  prod_rank(1,2)=({pr1},{pr2})")
    
    # Verify boolean equivalence
    if n <= 4:
        match = True
        for bits in cartprod([0,1], repeat=2*n):
            a = {j: bits[j] for j in range(2*n)}
            sv = poly_eval(s, a)
            pv = poly_eval(p, a)
            if (sv == 0) != (pv == 1):
                match = False
        print(f"         Boolean: ∑G=0 ⟺ ∏(1-G)=1? {match}")

# === Channel 2: ∑G² → ∏(1-G²) for multilinear G ===
print("\n--- Channel 2: ∑G² → ∏(1-G²) with AND gadgets ---")
print("G_i = x_{2i}·x_{2i+1}")
for n in range(2, 7):
    s = C(0)
    p = C(1)
    for i in range(n):
        g = gadget_and(i)
        g2 = poly_mul(g, g)  # In multilinear: (x·y)² = 0 (x²=0)
        s = poly_add(s, g2)
        p = poly_mul(p, poly_add(C(1), poly_neg(g2)))
    
    # g² is zero in multilinear! So use g directly
    s2 = C(0)
    p2 = C(1)
    for i in range(n):
        g = gadget_and(i)
        s2 = poly_add(s2, g)
        p2 = poly_mul(p2, poly_add(C(1), poly_neg(g)))
    
    sv = get_vars(s2)
    pv = get_vars(p2)
    sr = spdp_rank(s2, sv, 2) if len(sv) >= 2 else 0
    pr = spdp_rank(p2, pv, 2) if len(pv) >= 2 else 0
    print(f"  n={n}: sum_rank={sr}  prod_rank={pr}")

# === Channel 3: The KEY experiment ===
# Start from ∑G_i (sum), apply inclusion-exclusion to get ∏(1-G_i) (product)
# This is a NONLINEAR algebraic transformation.
# Question: what is its effect on SPDP rank?
print("\n--- Channel 3: Inclusion-exclusion as rank amplifier ---")
print("∑G_i has rank O(n). ∏(1-G_i) has rank C(n,κ).")
print("The map ∑ → ∏ is: f(S) = 1-S, applied per term, then multiply.")
print("This is EXACTLY the exponential/product map.")
print()
print("Can this be factored as a composition of rank-bounded operations?")
print("If NOT, then the map itself encodes the hardness.")
print()

# The inclusion-exclusion formula:
# ∏(1-G_i) = 1 - ∑G_i + ∑_{i<j}G_iG_j - ∑_{i<j<k}G_iG_jG_k + ...
# = ∑_{S⊆[n]} (-1)^|S| ∏_{i∈S} G_i
#
# This has EXPONENTIALLY many terms when G_i are general.
# But when G_i are multilinear with disjoint variables, each ∏G_i
# is a single monomial → the sum has 2^n terms → exponential degree.
#
# KEY INSIGHT: The inclusion-exclusion expansion IS the source of
# superpolynomial rank. It's not a "channel" — it's the computation
# itself. Going from sum to product requires exponential work.

print("Inclusion-exclusion expansion of ∏(1-G_i):")
for n in [2, 3, 4]:
    p = C(1)
    for i in range(n):
        p = poly_mul(p, poly_add(C(1), poly_neg(gadget_simple(i))))
    print(f"  n={n}: {len(p)} terms (2^n = {2**n})")
    if n <= 3:
        for m, c in sorted(p.items(), key=lambda x: (len(x[0]), x)):
            vars_str = '·'.join(f'x{v}' for v in sorted(m)) if m else '1'
            print(f"    {'+' if c > 0 else ''}{c}·{vars_str}")

# === Channel 4: Möbius function on satisfying assignments ===
print("\n--- Channel 4: Boolean interpolation ---")
print("Construct the UNIQUE multilinear polynomial matching a truth table.")
print("Both sum and product give the same truth table on {0,1}^n")
print("(modulo the semantic flip), so their multilinear extensions differ")
print("by exactly the inclusion-exclusion terms.")
print()

for n in [2, 3]:
    # Truth table: f(x) = 1 iff all G_i = 0 (all clauses satisfied)
    # G_i = x_{2i}, so satisfied when x_{2i} = 0
    # f(x) = ∏(1 - x_{2i}) — this IS the product form!
    
    # Same truth table via sum: f(x) = 1 - min(1, ∑x_{2i})
    # But min() isn't a polynomial. Over {0,1}:
    # f(x) = ∏(1-x_{2i}) is the ONLY multilinear polynomial matching this.
    
    # So the product form IS the multilinear interpolation of "all satisfied"
    # There is NO simpler polynomial over {0,1} — the product is canonical.
    
    p = C(1)
    for i in range(n):
        p = poly_mul(p, poly_add(C(1), poly_neg(X(2*i))))
    
    print(f"  n={n}: Unique multilinear poly for 'all satisfied':")
    print(f"         {len(p)} terms, rank(κ=2) = {spdp_rank(p, get_vars(p), 2)}")
    print(f"         This IS ∏(1-x_{{2i}}) — the product form is CANONICAL.")

print()
print("=" * 70)
print("SYNTHESIS")
print("=" * 70)
print("""
FINDINGS:

1. The inclusion-exclusion transform ∑G → ∏(1-G) converts sum to product.
   It's nonlinear (exponential map) and creates 2^n terms from n terms.
   This IS the rank amplification — it's not a "channel," it's the
   core computation.

2. Over {0,1}^n, the product form ∏(1-G_i) is the UNIQUE multilinear
   polynomial encoding "all clauses satisfied." There is no simpler
   multilinear representation of this boolean function.

3. The sum form ∑G_i is a DIFFERENT boolean function (counts violations).
   It's not "the same function in different representation" — it's a
   genuinely different polynomial computing a different thing.

4. The SPDP framework compares:
   - NP: the VERIFIER polynomial (product form) — high rank
   - P:  the COMPILED TM polynomial (sum of gate constraints) — low rank
   These are different objects computing different things.
   The extraction bridge must show that one "contains" the other.

5. The bridge would need: from ∑(gate_constraints)², recover ∏(1-z·G).
   This is inclusion-exclusion applied to the gate constraints.
   Inclusion-exclusion from n terms produces 2^n terms.
   A poly-time TM has poly(n) gates → 2^{poly(n)} = exponential terms.
   So the bridge computation itself is EXPONENTIAL.

6. CONCLUSION: The extraction bridge requires exponential work because
   it's literally computing the product from the sum via inclusion-
   exclusion. This is WHY the axiom can't be proved — it asserts
   that an exponential computation preserves polynomial rank bounds,
   but the computation itself destroys those bounds.
""")
