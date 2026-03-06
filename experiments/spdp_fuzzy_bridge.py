#!/usr/bin/env python3
"""
Fuzzy bridge search: generate multiple candidate coarse-graining channels,
test each for the property we need:

For a CORRECT solver, does the channel force high observable complexity
even when the polynomial is in sum form?

Candidates:
A. Boolean quotient (reduce mod x²=x, then measure rank)
B. Evaluation channel (average rank over boolean evaluation points)
C. Boolean Fourier (expand in ±1 basis, measure spectral support)
D. Partial trace (fix computation vars, measure clause-var rank)
E. Convolution channel (convolve product and sum, measure interaction)
F. Restriction to satisfying face (restrict to assignments satisfying k-1 clauses)
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
def X(i): return {frozenset([i]):1}
def C(c): return {frozenset():c} if c else {}

def pderiv(p,v):
    r=defaultdict(int)
    for m,c in p.items():
        if v in m: r[m-{v}]+=c
    return {m:c for m,c in r.items() if c}

def poly_eval(p, assignment):
    """Evaluate polynomial at assignment dict {var: value}."""
    result = 0
    for m, c in p.items():
        val = c
        for v in m:
            if v in assignment:
                val *= assignment[v]
            else:
                return None  # has free variables
        result += val
    return result

def poly_partial_eval(p, assignment):
    """Partially evaluate: fix some variables, leave others symbolic."""
    result = defaultdict(int)
    for m, c in p.items():
        val = c
        remaining = set()
        for v in m:
            if v in assignment:
                val *= assignment[v]
            else:
                remaining.add(v)
        result[frozenset(remaining)] += val
    return {m:c for m,c in result.items() if c}

def boolean_reduce(p):
    """Reduce polynomial mod x²=x for all variables (multilinearize)."""
    # Already multilinear in our representation (frozenset keys), so just return
    return p

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

# === Builders ===
def productPoly(n):
    p=C(1)
    for i in range(n):
        g=poly_add(X(2*i),X(2*i+1))
        p=poly_mul(p, poly_add(C(1), poly_neg(poly_mul(X(1000+i),g))))
    return p

def sumPoly(n):
    p={}
    for i in range(n):
        g=poly_add(X(2*i),X(2*i+1))
        p=poly_add(p,poly_mul(g,g))
    return p

def tmCompiledPoly(n):
    """
    Simulate a TM that checks Tseitin clauses sequentially.
    State vars: q_t (3000+t), input vars: x_j (0..2n-1)
    Gate_t: q_t · (x_{2t} + x_{2t+1} - 1) — checks clause t
    Compiled: ∑_t (gate_t)²
    
    If TM is correct, gate_t = 0 iff clause t is satisfied.
    """
    p = {}
    for t in range(n):
        gate = poly_mul(X(3000+t), poly_add(poly_add(X(2*t), X(2*t+1)), C(-1)))
        p = poly_add(p, poly_mul(gate, gate))
    return p

# === Channel A: Boolean Fourier transform ===
def boolean_fourier_support(p, variables):
    """
    Compute Fourier expansion over {0,1}^n.
    f(x) = ∑_S f̂(S) · χ_S(x) where χ_S(x) = ∏_{i∈S} (-1)^{x_i}
    f̂(S) = (1/2^n) ∑_x f(x) · χ_S(x)
    
    Count nonzero Fourier coefficients (spectral support size).
    """
    n = len(variables)
    if n > 12: return -1  # too big
    
    # Evaluate p at all boolean points
    vals = {}
    for bits in cartprod([0,1], repeat=n):
        assignment = {variables[i]: bits[i] for i in range(n)}
        v = poly_eval(p, assignment)
        if v is None: return -1
        vals[bits] = v
    
    # Compute Fourier coefficients
    nonzero = 0
    for subset_size in range(n+1):
        for S in combinations(range(n), subset_size):
            S_set = set(S)
            fhat = 0
            for bits in cartprod([0,1], repeat=n):
                chi = 1
                for i in S_set:
                    chi *= (-1)**bits[i]
                fhat += vals[bits] * chi
            fhat /= 2**n
            if abs(fhat) > 1e-10:
                nonzero += 1
    return nonzero

# === Channel B: Partial evaluation + rank ===
def partial_eval_rank(p, fix_vars, fix_vals, free_vars, kappa):
    """Fix some variables, compute SPDP rank on remaining."""
    assignment = dict(zip(fix_vars, fix_vals))
    p_restricted = poly_partial_eval(p, assignment)
    return spdp_rank(p_restricted, free_vars, kappa)

# === Channel C: Average rank over boolean evaluations of auxiliary vars ===
def avg_rank_over_aux(p, aux_vars, content_vars, kappa, max_samples=32):
    """Average SPDP rank when auxiliary variables are set to boolean values."""
    n_aux = len(aux_vars)
    if n_aux > 5:
        # Sample randomly
        np.random.seed(42)
        samples = [tuple(np.random.randint(0,2,n_aux)) for _ in range(max_samples)]
    else:
        samples = list(cartprod([0,1], repeat=n_aux))
    
    ranks = []
    for bits in samples:
        assignment = {aux_vars[i]: bits[i] for i in range(n_aux)}
        p_rest = poly_partial_eval(p, assignment)
        r = spdp_rank(p_rest, content_vars, kappa)
        ranks.append(r)
    return np.mean(ranks), np.max(ranks)

# === Channel D: Restriction to satisfying face ===
def satisfying_face_rank(p, n_clauses, kappa):
    """
    Fix content variables to a satisfying assignment,
    measure rank over auxiliary variables.
    
    Satisfying: x_{2i} = 1, x_{2i+1} = 0 for all i
    (each clause x_{2i}+x_{2i+1} = 1, satisfied)
    """
    assignment = {}
    for i in range(n_clauses):
        assignment[2*i] = 1
        assignment[2*i+1] = 0
    p_rest = poly_partial_eval(p, assignment)
    # What vars remain?
    remaining = sorted(set().union(*(m for m in p_rest.keys() if m)))
    if not remaining: return 0
    return spdp_rank(p_rest, remaining, kappa)


# ===========================================================
print("=" * 70)
print("FUZZY BRIDGE: Multi-channel search")
print("=" * 70)

# Channel A: Fourier support
print("\n--- Channel A: Boolean Fourier support ---")
print("(Number of nonzero Fourier coefficients)")
print(f"{'n':>3} {'product':>10} {'sum':>10} {'tm_compiled':>12}")
for n in range(2, 6):
    x_vars = list(range(2*n))
    # For product, also has z vars — evaluate as function of ALL vars
    pp = productPoly(n)
    pp_vars = sorted(set().union(*(m for m in pp.keys() if m)))
    sp = sumPoly(n)
    sp_vars = list(range(2*n))
    tp = tmCompiledPoly(n)
    tp_vars = sorted(set().union(*(m for m in tp.keys() if m)))
    
    pf = boolean_fourier_support(pp, pp_vars)
    sf = boolean_fourier_support(sp, sp_vars)
    tf = boolean_fourier_support(tp, tp_vars)
    print(f"{n:>3} {pf:>10} {sf:>10} {tf:>12}")

# Channel B: Fix z/q vars to 1, measure x-var rank
print("\n--- Channel B: Fix auxiliary vars to 1, rank over content vars ---")
print(f"{'n':>3} {'prod(z=1)':>10} {'tm(q=1)':>10} {'sum':>10}  (κ=1)")
for n in range(2, 7):
    pp = productPoly(n)
    z_fixed = {1000+i: 1 for i in range(n)}
    pp_rest = poly_partial_eval(pp, z_fixed)
    x_vars = list(range(2*n))
    pr = spdp_rank(pp_rest, x_vars, 1)
    
    tp = tmCompiledPoly(n)
    q_fixed = {3000+t: 1 for t in range(n)}
    tp_rest = poly_partial_eval(tp, q_fixed)
    tr = spdp_rank(tp_rest, x_vars, 1)
    
    sp = sumPoly(n)
    sr = spdp_rank(sp, x_vars, 1)
    
    print(f"{n:>3} {pr:>10} {tr:>10} {sr:>10}")

# Channel C: Average rank over boolean aux settings
print("\n--- Channel C: Average SPDP rank over boolean aux settings ---")
print(f"{'n':>3} {'prod_avg':>10} {'prod_max':>10} {'tm_avg':>10} {'tm_max':>10}  (κ=1)")
for n in range(2, 6):
    pp = productPoly(n)
    z_vars = list(range(1000, 1000+n))
    x_vars = list(range(2*n))
    pa, pm = avg_rank_over_aux(pp, z_vars, x_vars, 1)
    
    tp = tmCompiledPoly(n)
    q_vars = list(range(3000, 3000+n))
    ta, tm_ = avg_rank_over_aux(tp, q_vars, x_vars, 1)
    
    print(f"{n:>3} {pa:>10.1f} {pm:>10} {ta:>10.1f} {tm_:>10}")

# Channel D: Satisfying face
print("\n--- Channel D: Rank on satisfying face (x=satisfying, rank over z/q) ---")
print(f"{'n':>3} {'prod_sat':>10} {'tm_sat':>10}  (κ=1)")
for n in range(2, 7):
    pr = satisfying_face_rank(productPoly(n), n, 1)
    tr = satisfying_face_rank(tmCompiledPoly(n), n, 1)
    print(f"{n:>3} {pr:>10} {tr:>10}")

# Channel E: THE KEY — content-only rank after boolean quotient
# Reduce both to same variable set, compare
print("\n--- Channel E: Same content vars, after fixing aux to const ---")
print("Product (z_i=1) vs TM compiled (q_t=1): same content polynomial?")
for n in range(2, 5):
    pp = productPoly(n)
    pp_rest = poly_partial_eval(pp, {1000+i: 1 for i in range(n)})
    
    tp = tmCompiledPoly(n)
    tp_rest = poly_partial_eval(tp, {3000+t: 1 for t in range(n)})
    
    sp = sumPoly(n)
    
    print(f"\n  n={n}:")
    print(f"    product|z=1 = {dict(pp_rest)}")
    print(f"    tm|q=1      = {dict(tp_rest)}")
    print(f"    sum         = {dict(sp)}")
    
    # Are product|z=1 and sum the same?
    diff = poly_add(pp_rest, poly_neg(sp))
    print(f"    prod|z=1 - sum = {dict(diff) if diff else 'ZERO (identical!)'}")

print("\n" + "=" * 70)
print("FUZZY SELECTION: Which channel preserves the bridge?")
print("=" * 70)
