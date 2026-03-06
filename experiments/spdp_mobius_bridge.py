#!/usr/bin/env python3
"""
Möbius + SPDP integration.

Key findings so far:
1. Rank explosion happens at Möbius level 2 (pairwise interactions)
2. Chain (TM-style) has lower rank than disjoint (Tseitin-style)
3. Need to connect this to SPDP framework

Idea: Define Möbius-SPDP rank as SPDP rank of the multilinear
extension of the boolean function computed by p.

If P=NP, the solver TM M* computes f(x) = "all clauses satisfied".
The unique multilinear extension of f is ∏(1-G_C).
This has superpolynomial SPDP rank.

The compiled polynomial P_{M*}, when restricted to the correct
computation trace, agrees with f on {0,1}^n.
Restriction is rank-monotone: rank(p|_{fix}) ≤ rank(p).

So: superpoly = rank(∏(1-G_C)) = rank(multilinear(f))
                                ≤ rank(P_{M*}|_{trace})
                                ≤ rank(P_{M*})
                                ≤ poly (P-side collapse)
Contradiction.

KEY QUESTION: Does rank(multilinear(f)) ≤ rank(P_{M*}|_{trace})?
This requires: restricting to trace gives a polynomial whose SPDP rank
is at least as large as the multilinear extension.

TEST THIS.
"""
import numpy as np
from itertools import combinations, product as cartprod
from collections import defaultdict

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

def poly_partial_eval(p, assignment):
    result = defaultdict(int)
    for m, c in p.items():
        val = c
        remaining = set()
        for v in m:
            if v in assignment:
                val *= assignment[v]
            else:
                remaining.add(v)
        if val: result[frozenset(remaining)] += val
    return {m:c for m,c in result.items() if c}

def poly_eval_bool(p, variables):
    """Evaluate on all boolean inputs, return truth table."""
    n = len(variables)
    table = {}
    for bits in cartprod([0,1], repeat=n):
        a = {variables[i]: bits[i] for i in range(n)}
        val = 0
        for m, c in p.items():
            v = c
            for var in m:
                v *= a.get(var, 0)
            val += v
        table[bits] = val
    return table

def multilinear_from_truth_table(table, variables):
    """
    Construct the unique multilinear polynomial matching a truth table.
    Uses Möbius inversion on the boolean lattice.
    
    f(x) = ∑_{S⊆[n]} c_S · ∏_{i∈S} x_i
    where c_S = ∑_{T⊆S} (-1)^{|S|-|T|} f(T)
    """
    n = len(variables)
    poly = {}
    for subset_size in range(n+1):
        for S in combinations(range(n), subset_size):
            S_set = set(S)
            # Möbius inversion coefficient
            c_S = 0
            for sub_size in range(subset_size+1):
                for T in combinations(list(S), sub_size):
                    T_set = set(T)
                    # Evaluate f at the point where T-vars are 1, rest 0
                    point = tuple(1 if i in T_set else 0 for i in range(n))
                    c_S += ((-1)**(subset_size - sub_size)) * table[point]
            if c_S != 0:
                monom = frozenset(variables[i] for i in S)
                poly[monom] = c_S
    return poly

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
    return sorted(set().union(*(m for m in p.keys() if m))) if p else []

print("=" * 70)
print("MÖBIUS-SPDP BRIDGE: Multilinear Extension Test")
print("=" * 70)

# === Test 1: Multilinear extension of "all satisfied" ===
print("\n--- Test 1: Multilinear extension = product form ---")
print("f(x) = 1 iff all G_i = 0, where G_i = x_{2i} (clause i satisfied when x_{2i}=0)")
print()

for n in range(2, 6):
    variables = list(range(2*n))  # only even vars matter for this gadget
    # But let's use all vars for generality
    
    # Product form: ∏(1-x_{2i})
    prod = C(1)
    for i in range(n):
        prod = poly_mul(prod, poly_add(C(1), poly_neg(X(2*i))))
    
    # Truth table of "all satisfied"
    table = poly_eval_bool(prod, variables)
    
    # Multilinear extension from truth table
    ml = multilinear_from_truth_table(table, variables)
    
    # Compare
    diff = poly_add(prod, poly_neg(ml))
    same = not diff
    
    pv = get_vars(prod)
    pr = spdp_rank(prod, pv, 2) if len(pv) >= 2 else 0
    mv = get_vars(ml)
    mr = spdp_rank(ml, mv, 2) if len(mv) >= 2 else 0
    
    print(f"  n={n}: product_rank2={pr}  multilinear_rank2={mr}  identical={same}")

# === Test 2: TM compiled polynomial restricted to correct trace ===
print("\n--- Test 2: Restriction to correct trace ---")
print("TM compiles as ∑(q_t · gate_t)², restrict q_t to correct values")
print()

# Model: gate_t checks clause t. gate_t = x_{2t} (clause satisfied when x_{2t}=0)
# Correct trace: q_t = 1 for all t (TM runs all steps)
# P_{M*} = ∑(q_t · x_{2t})²  [non-multilinear: has x_{2t}² terms]
# In multilinear ring: (q_t · x_{2t})² → q_t · x_{2t} (since q²=q, x²=x, and q·x·q·x = q·x)
# Wait, in multilinear: (q·x)² = 0 because q·x·q·x requires q² which vanishes

# Use non-multilinear arithmetic for this test
def poly_mul_full(p1, p2):
    """Non-multilinear multiplication (allow x² etc.)."""
    r = defaultdict(int)
    for m1, c1 in p1.items():
        for m2, c2 in p2.items():
            # Merge monomials (allow overlap → higher powers)
            combined = defaultdict(int)
            for v in m1: combined[v] += 1
            for v in m2: combined[v] += 1
            key = frozenset(combined.items())
            r[key] += c1 * c2
    return {m: c for m, c in r.items() if c}

def multilinearize(p):
    """Reduce modulo x²=x: replace all powers > 1 with power 1."""
    r = defaultdict(int)
    for m, c in p.items():
        if isinstance(m, frozenset) and all(isinstance(x, tuple) for x in m):
            # m is frozenset of (var, power) tuples
            new_m = frozenset((v, 1) for v, pw in m)
            r[new_m] += c
        else:
            r[m] += c
    return {m: c for m, c in r.items() if c}

# Simpler approach: just evaluate the compiled polynomial on boolean inputs
# and construct its multilinear extension

for n in range(2, 6):
    content_vars = list(range(n))  # x_0, ..., x_{n-1} (one per clause)
    
    # "All satisfied" function: f(x) = 1 iff all x_i = 0
    # (clause i satisfied when x_i = 0)
    all_sat_table = {}
    for bits in cartprod([0,1], repeat=n):
        all_sat_table[bits] = 1 if all(b == 0 for b in bits) else 0
    
    # Multilinear extension of "all satisfied"
    ml_all_sat = multilinear_from_truth_table(all_sat_table, content_vars)
    
    # "Violation count" function: g(x) = ∑x_i (counts unsatisfied clauses)
    viol_table = {}
    for bits in cartprod([0,1], repeat=n):
        viol_table[bits] = sum(bits)
    
    ml_viol = multilinear_from_truth_table(viol_table, content_vars)
    
    # "Violation indicator" function: h(x) = 1 if any x_i=1, else 0
    # = 1 - ∏(1-x_i) = 1 - f(x)
    viol_ind_table = {}
    for bits in cartprod([0,1], repeat=n):
        viol_ind_table[bits] = 0 if all(b == 0 for b in bits) else 1
    
    ml_viol_ind = multilinear_from_truth_table(viol_ind_table, content_vars)
    
    r_sat = spdp_rank(ml_all_sat, content_vars, 2) if n >= 2 else 0
    r_viol = spdp_rank(ml_viol, content_vars, 2) if n >= 2 else 0
    r_vind = spdp_rank(ml_viol_ind, content_vars, 2) if n >= 2 else 0
    
    print(f"  n={n}:")
    print(f"    all_sat = ∏(1-x_i):     rank2={r_sat}  terms={len(ml_all_sat)}")
    print(f"    viol_count = ∑x_i:       rank2={r_viol}  terms={len(ml_viol)}")
    print(f"    viol_ind = 1-∏(1-x_i):   rank2={r_vind}  terms={len(ml_viol_ind)}")

# === Test 3: THE KEY — restriction rank monotonicity ===
print("\n--- Test 3: Restriction is rank-monotone ---")
print("rank(p|_{x_i=c}) ≤ rank(p)?")
print()

for n in [3, 4, 5]:
    # Product polynomial with extra variable
    p = C(1)
    for i in range(n):
        p = poly_mul(p, poly_add(C(1), poly_neg(poly_mul(X(100+i), X(i)))))
    
    av = get_vars(p)
    full_rank = spdp_rank(p, av, 2)
    
    # Restrict x_100 = 1 (fix first auxiliary var)
    p_rest = poly_partial_eval(p, {100: 1})
    rv = get_vars(p_rest)
    rest_rank = spdp_rank(p_rest, rv, 2) if len(rv) >= 2 else 0
    
    # Restrict all aux vars = 1
    fix_all = {100+i: 1 for i in range(n)}
    p_rest_all = poly_partial_eval(p, fix_all)
    rav = get_vars(p_rest_all)
    rest_all_rank = spdp_rank(p_rest_all, rav, 2) if len(rav) >= 2 else 0
    
    print(f"  n={n}: full_rank={full_rank}  fix1_rank={rest_rank}  fixAll_rank={rest_all_rank}")
    print(f"         monotone? full≥fix1: {full_rank >= rest_rank}  fix1≥fixAll: {rest_rank >= rest_all_rank}")

# === Test 4: BRIDGE ARGUMENT ===
print("\n" + "=" * 70)
print("BRIDGE ARGUMENT TEST")
print("=" * 70)
print()

for n in [3, 4, 5]:
    content_vars = list(range(n))
    
    # Step 1: NP side — multilinear extension of "all satisfied"
    prod = C(1)
    for i in range(n):
        prod = poly_mul(prod, poly_add(C(1), poly_neg(X(i))))
    np_rank = spdp_rank(prod, content_vars, 2)
    
    # Step 2: P side — compiled TM polynomial
    # TM has n gates, each checking one clause.
    # Gate variables: q_t (state at time t), x_i (clause var)
    # P_compiled = ∑_t (q_t · x_t)  [simplified: sum of gate outputs]
    # Actually in sum-of-squares: ∑(q_t · x_t)²
    # In multilinear: (q_t · x_t)² = q_t · x_t (since multilinear)
    # So P_compiled_ml = ∑ q_t · x_t
    
    compiled = {}
    all_vars_compiled = []
    for t in range(n):
        compiled = poly_add(compiled, poly_mul(X(100+t), X(t)))
        all_vars_compiled.extend([100+t, t])
    all_vars_compiled = sorted(set(all_vars_compiled))
    
    compiled_rank = spdp_rank(compiled, all_vars_compiled, 2)
    
    # Step 3: Restrict compiled to correct trace (q_t = 1)
    restricted = poly_partial_eval(compiled, {100+t: 1 for t in range(n)})
    # restricted = ∑ x_t
    rest_vars = get_vars(restricted)
    restricted_rank = spdp_rank(restricted, rest_vars, 2) if len(rest_vars) >= 2 else 0
    
    # Step 4: Multilinear extension of the boolean function computed by restricted
    rest_table = poly_eval_bool(restricted, content_vars)
    ml_rest = multilinear_from_truth_table(rest_table, content_vars)
    ml_rank = spdp_rank(ml_rest, content_vars, 2) if n >= 2 else 0
    
    # The restricted polynomial computes ∑x_i (violation count)
    # Its truth table: gives count of 1s
    # Multilinear extension: ∑x_i (it's already multilinear!)
    # SPDP rank of ∑x_i at κ=2: derivatives ∂²(∑x_i)/∂x_a∂x_b = 0
    # So rank = 0 at κ≥2!
    
    # But "all satisfied" indicator ∏(1-x_i) has rank C(n,2) at κ=2.
    # These are DIFFERENT boolean functions!
    # ∑x_i computes violation COUNT, not satisfaction INDICATOR.
    
    print(f"  n={n}:")
    print(f"    NP (∏(1-x_i)):           rank2={np_rank}")
    print(f"    Compiled (∑q_t·x_t):     rank2={compiled_rank}")
    print(f"    Restricted (∑x_t):       rank2={restricted_rank}")
    print(f"    ML of restricted func:   rank2={ml_rank}")
    print(f"    ML of ALL-SAT function:  rank2={np_rank}")
    print()
    print(f"    restricted computes ∑x_i (violation count)")
    print(f"    NP verifier computes ∏(1-x_i) (all-satisfied indicator)")
    print(f"    DIFFERENT functions → DIFFERENT multilinear extensions!")
    print()
    
    # What if we use indicator of "restricted = 0"?
    indicator_table = {bits: (1 if rest_table[bits] == 0 else 0) for bits in rest_table}
    ml_indicator = multilinear_from_truth_table(indicator_table, content_vars)
    ind_rank = spdp_rank(ml_indicator, content_vars, 2) if n >= 2 else 0
    
    # This indicator function IS "all satisfied" = ∏(1-x_i)
    diff = poly_add(ml_indicator, poly_neg(prod))
    is_same = not diff
    
    print(f"    Indicator(restricted=0): rank2={ind_rank}  same_as_product={is_same}")
    print(f"    ∏(1-x_i) terms: {sorted(prod.items())}")
    print(f"    indicator terms: {sorted(ml_indicator.items())}")
    print()

print("=" * 70)
print("SYNTHESIS: Can Möbius + SPDP work?")
print("=" * 70)
