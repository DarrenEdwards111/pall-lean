#!/usr/bin/env python3
"""
Markov Bridge for SPDP — translating between NP and P derivative worlds.

Key idea: Instead of an algebraic map between POLYNOMIALS,
build a LINEAR MAP (channel) between DERIVATIVE SPACES.

The channel corresponds to the fact that if M* solves SAT,
it must internally simulate/verify each clause. This creates
a correspondence between NP variables (clause-indexed, disjoint)
and P variables (time-indexed, sequential).

The bridge is a matrix T: V_NP → V_P such that:
  rank(image of NP generators under T) ≤ rank(P generators)

If T is injective on the NP derivative space, we get:
  rank_NP ≤ rank_P

Testing multiple channel designs to find one that works.
"""

import numpy as np
from itertools import combinations
from collections import defaultdict

# === Polynomial arithmetic (multilinear) ===
def poly_mul(p1, p2):
    result = defaultdict(int)
    for m1, c1 in p1.items():
        for m2, c2 in p2.items():
            if m1 & m2: continue
            result[m1 | m2] += c1 * c2
    return {m: c for m, c in result.items() if c != 0}

def poly_add(p1, p2):
    result = defaultdict(int)
    for m, c in p1.items(): result[m] += c
    for m, c in p2.items(): result[m] += c
    return {m: c for m, c in result.items() if c != 0}

def poly_neg(p): return {m: -c for m, c in p.items()}
def X(i): return {frozenset([i]): 1}
def C(c): return {frozenset(): c} if c else {}

def pderiv(p, v):
    result = defaultdict(int)
    for m, c in p.items():
        if v in m: result[m - {v}] += c
    return {m: c for m, c in result.items() if c != 0}

def get_all_vars(p):
    return sorted(set().union(*(m for m in p.keys() if m)))

def derivative_vectors(poly, variables, kappa):
    """
    Return list of (combo, derivative_dict) for all kappa-fold derivatives.
    """
    results = []
    for combo in combinations(variables, kappa):
        d = poly
        for v in combo:
            d = pderiv(d, v)
            if not d: break
        if d:
            results.append((combo, d))
    return results

def vectors_to_matrix(derivs_list):
    """Convert list of derivative dicts to a coefficient matrix."""
    if not derivs_list:
        return np.zeros((0, 0))
    all_m = sorted(set().union(*(d.keys() for d in derivs_list)),
                   key=lambda s: (len(s), tuple(sorted(s))))
    mi = {m: i for i, m in enumerate(all_m)}
    mat = np.zeros((len(derivs_list), len(all_m)))
    for i, d in enumerate(derivs_list):
        for m, c in d.items():
            mat[i, mi[m]] = c
    return mat, all_m

def rank(mat):
    if mat.size == 0: return 0
    return int(np.linalg.matrix_rank(mat))


# === Build NP polynomial (Tseitin-style) ===
def build_np_poly(n_clauses):
    """
    Q = ∏_{i=0}^{n-1} (1 - z_i · G_i)
    z_i = var 1000+i (independent per clause)
    G_i = x_{2i} + x_{2i+1} (width-2 gadget, vars 0..2n-1)
    """
    p = C(1)
    for i in range(n_clauses):
        z_i = X(1000 + i)
        G_i = poly_add(X(2*i), X(2*i + 1))
        factor = poly_add(C(1), poly_neg(poly_mul(z_i, G_i)))
        p = poly_mul(p, factor)
    np_vars = list(range(2*n_clauses)) + list(range(1000, 1000+n_clauses))
    return p, sorted(np_vars)

def build_p_poly_sequential(n_clauses):
    """
    P-side: TM checking clauses sequentially.
    At time t, TM checks clause t using state q_t and reads x_{2t}, x_{2t+1}.
    
    Gate_t = (1 - q_t · (x_{2t} + x_{2t+1})) · (1 - q_t · q_{t+1,accept})
    
    Simplified model: ∏_t (1 - q_t · G_t)
    where q_t = var 2000+t (STATE at time t, sequential, each used once)
    and G_t uses x_{2t}, x_{2t+1} (same content vars as NP side)
    
    KEY: q_t are FRESH per time step (like z_i in NP side!)
    """
    p = C(1)
    for t in range(n_clauses):
        q_t = X(2000 + t)
        G_t = poly_add(X(2*t), X(2*t + 1))
        factor = poly_add(C(1), poly_neg(poly_mul(q_t, G_t)))
        p = poly_mul(p, factor)
    p_vars = list(range(2*n_clauses)) + list(range(2000, 2000+n_clauses))
    return p, sorted(p_vars)

def build_p_poly_shared_state(n_clauses):
    """
    P-side with shared state: TM reuses same state variable.
    ∏_t (1 - q · G_t) where q is shared.
    """
    p = C(1)
    q = X(3000)
    for t in range(n_clauses):
        G_t = poly_add(X(2*t), X(2*t + 1))
        factor = poly_add(C(1), poly_neg(poly_mul(q, G_t)))
        p = poly_mul(p, factor)
    p_vars = [3000] + list(range(2*n_clauses))
    return p, sorted(p_vars)


# === Markov Bridge Designs ===

def markov_bridge_relabel(np_derivs, np_vars, p_derivs, p_vars, n_clauses):
    """
    Bridge Design 1: Simple variable relabeling.
    Map z_i (NP, var 1000+i) → q_i (P, var 2000+i)
    Content vars (x_j) stay the same.
    
    This is a bijection on the derivative space if the polynomial
    structure is the same up to relabeling.
    """
    # Build the relabeling: 1000+i → 2000+i, x_j → x_j
    var_map = {}
    for i in range(n_clauses):
        var_map[1000 + i] = 2000 + i  # z_i → q_i
    for j in range(2 * n_clauses):
        var_map[j] = j  # x_j → x_j
    
    # Apply relabeling to NP derivative vectors
    remapped = []
    for combo, d in np_derivs:
        new_d = {}
        for m, c in d.items():
            new_m = frozenset(var_map.get(v, v) for v in m)
            new_d[new_m] = c
        remapped.append(new_d)
    
    return remapped

def markov_bridge_coarse(np_derivs, np_vars, p_derivs, p_vars, n_clauses):
    """
    Bridge Design 2: Coarse-graining channel.
    Multiple P-variables map to single NP-variable.
    
    Like the refinement channel in the quantum paper:
    partial trace over internal TM variables.
    """
    # Map: sum of derivatives w.r.t. TM vars → single NP derivative
    # This is a surjective linear map
    pass  # TODO after testing design 1

def markov_bridge_stochastic(np_derivs, p_poly, p_vars, n_clauses):
    """
    Bridge Design 3: Stochastic matrix.
    
    Build transition matrix T where T[i,j] gives the "weight"
    of NP generator i in P generator j.
    
    T is constructed from the inner product of derivative vectors.
    If T has rank ≥ rank(NP generators), the bridge works.
    """
    pass  # TODO


# === Main Experiments ===
print("=" * 70)
print("MARKOV BRIDGE EXPERIMENTS")
print("=" * 70)

# Experiment 1: NP vs P(fresh state) — should be isomorphic
print("\n--- Exp 1: NP (indep z_i) vs P (fresh q_t per step) ---")
print("If TM uses fresh state var per step, it's isomorphic to verifier!")
print(f"{'n':>4} {'NP κ=2':>8} {'P(fresh) κ=2':>13} {'iso?':>6}")
for n in range(2, 7):
    np_p, np_v = build_np_poly(n)
    p_p, p_v = build_p_poly_sequential(n)
    
    np_r = rank(vectors_to_matrix([d for _, d in derivative_vectors(np_p, np_v, 2)])[0])
    p_r = rank(vectors_to_matrix([d for _, d in derivative_vectors(p_p, p_v, 2)])[0])
    
    print(f"{n:>4} {np_r:>8} {p_r:>13} {'YES' if np_r == p_r else 'NO':>6}")

# Experiment 2: NP vs P(shared state) — the problematic case
print("\n--- Exp 2: NP (indep z_i) vs P (shared q) ---")
print("Shared state kills rank. Can a bridge recover it?")
print(f"{'n':>4} {'NP κ=2':>8} {'P(shared) κ=2':>14}")
for n in range(2, 7):
    np_p, np_v = build_np_poly(n)
    p_p, p_v = build_p_poly_shared_state(n)
    
    np_r = rank(vectors_to_matrix([d for _, d in derivative_vectors(np_p, np_v, 2)])[0])
    p_r = rank(vectors_to_matrix([d for _, d in derivative_vectors(p_p, p_v, 2)])[0])
    
    print(f"{n:>4} {np_r:>8} {p_r:>14}")

# Experiment 3: The key question — does TM compilation ACTUALLY share state?
print("\n--- Exp 3: Realistic TM compilation ---")
print("""
In a real TM arithmetization:
- q_{t,s} = state indicator at time t, state s
- a_{t,p} = tape symbol at time t, position p  
- h_{t,p} = head position at time t, position p

Each variable is INDEXED BY TIME → naturally disjoint across steps.
Gate_t involves: q_{t,*}, q_{t+1,*}, a_{t,h}, a_{t+1,h}, h_{t,*}, h_{t+1,*}

So gate_t and gate_{t+2} share NO variables (2-step gap = disjoint).
This means ⌊T/2⌋ disjoint factors exist → superpoly rank.

CONCLUSION: A real TM compiled polynomial has superpoly SPDP rank
in product form, just like the NP verifier.
Both sides are superpoly → no contradiction → SPDP alone doesn't separate.

UNLESS the Markov bridge changes the RANK MEASURE, not the polynomial.
""")

# Experiment 4: Markov channel as rank measure modifier
print("--- Exp 4: Channel-modified rank ---")
print("""
Idea: Define rank_M(P) = rank of T(derivative_space(P))
where T is a Markov channel (stochastic matrix on monomials).

If T "blurs" the P-side derivatives (collapsing them),
the channel-modified rank could be polynomial.
If T "preserves" the NP-side derivatives,
the channel-modified rank stays superpolynomial.

The channel T encodes the STRUCTURE of the computation,
not just the algebra. Different computations (verifier vs solver)
have different channel-modified ranks.
""")

# Build channel: random stochastic matrix for now, then structured
for n in [3, 4, 5]:
    np_p, np_v = build_np_poly(n)
    np_derivs = derivative_vectors(np_p, np_v, 2)
    if not np_derivs:
        continue
    
    np_mat, np_monoms = vectors_to_matrix([d for _, d in np_derivs])
    np_rank = rank(np_mat)
    
    # Channel 1: Identity (no modification)
    id_rank = np_rank
    
    # Channel 2: Random projection to lower dimension
    np.random.seed(42)
    k_target = min(n, np_mat.shape[1])
    if np_mat.shape[1] > 0 and k_target > 0:
        proj = np.random.randn(np_mat.shape[1], k_target)
        projected = np_mat @ proj
        proj_rank = rank(projected)
    else:
        proj_rank = 0
    
    # Channel 3: Coarse-grain monomials by total degree
    # Group monomials by |support|, sum coefficients within groups
    degree_groups = defaultdict(list)
    for j, m in enumerate(np_monoms):
        degree_groups[len(m)].append(j)
    n_groups = len(degree_groups)
    coarse_mat = np.zeros((np_mat.shape[0], n_groups))
    for gi, (deg, cols) in enumerate(sorted(degree_groups.items())):
        coarse_mat[:, gi] = np_mat[:, cols].sum(axis=1)
    coarse_rank = rank(coarse_mat)
    
    print(f"  n={n}: NP_rank={np_rank}, proj_rank={proj_rank}, coarse_rank={coarse_rank}")

# Experiment 5: The refinement channel idea
print("\n--- Exp 5: Refinement channel (à la quantum paper) ---")
print("""
In your quantum paper, the refinement channel worked because:
1. Raw overlap S_min = 0 (equivalent to: direct extraction fails)
2. Partial trace over outer shell → S_coarse = 2.0 (equivalent to: channel fixes it)

For SPDP, the analogous construction:
1. Raw extraction: rank(NP) > rank(P) — direct transfer fails
2. Channel: partial trace over "auxiliary" variables → modified rank transfers

The channel would trace out the z_C / q_t variables (auxiliary)
and keep only the content variables (x_e / tape symbols).

Let's test: what is the SPDP rank restricted to content variables only?
""")

for n in range(2, 7):
    np_p, np_v = build_np_poly(n)
    p_shared, p_sv = build_p_poly_shared_state(n)
    
    # Content variables only: 0..2n-1
    content_vars = list(range(2*n))
    
    np_content_derivs = derivative_vectors(np_p, content_vars, 2)
    p_content_derivs = derivative_vectors(p_shared, content_vars, 2)
    
    if np_content_derivs:
        np_cm, _ = vectors_to_matrix([d for _, d in np_content_derivs])
        np_cr = rank(np_cm)
    else:
        np_cr = 0
    
    if p_content_derivs:
        p_cm, _ = vectors_to_matrix([d for _, d in p_content_derivs])
        p_cr = rank(p_cm)
    else:
        p_cr = 0
    
    # Also check: NP with ALL vars, P with ALL vars
    np_all = derivative_vectors(np_p, np_v, 2)
    p_all = derivative_vectors(p_shared, p_sv, 2)
    np_ar = rank(vectors_to_matrix([d for _, d in np_all])[0]) if np_all else 0
    p_ar = rank(vectors_to_matrix([d for _, d in p_all])[0]) if p_all else 0
    
    print(f"  n={n}: NP(all)={np_ar} NP(content)={np_cr} | P(all)={p_ar} P(content)={p_cr}")

print("\n" + "=" * 70)
print("KEY QUESTION: Is there a channel where rank_channel(NP) > rank_channel(P)?")
print("=" * 70)
